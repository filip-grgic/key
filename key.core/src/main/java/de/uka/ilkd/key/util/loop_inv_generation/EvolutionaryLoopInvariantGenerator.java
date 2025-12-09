package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.speclang.BasicLoopSpecificationImpl;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.engine.ProofSearchInformation;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class EvolutionaryLoopInvariantGenerator {

    private final Services services;

    public EvolutionaryLoopInvariantGenerator(Services services) {
        this.services = services;
    }

    public void generateLoopInvariant() {
        JTerm[] verificationConditions = generateVerificationConditions();
    }

    private JTerm[] generateVerificationConditions() {
        ProofEnvironment proofEnv = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
        Services envServices = proofEnv.getServicesForEnvironment();
        TermBuilder envTermBuilder = envServices.getTermBuilder();
        Sequent runningSequent = services.getProof().openGoals().head().sequent();


        // Get all program variables and extract their sorts for the fresh invariant
        LocationVariable[] locationVariables = collectAllProgramVariables(runningSequent);
        Sort[] predicateParameterSorts =  new Sort[locationVariables.length];
        JTerm[] predicateParameterTerms = new JTerm[locationVariables.length];

        for (int i = 0; i < locationVariables.length; i++) {
            predicateParameterSorts[i] = locationVariables[i].sort();
            predicateParameterTerms[i] = envTermBuilder.var(locationVariables[i]);
        }

        List<LoopSpecification> loopSpecs = new ArrayList<>();
        Sequent sideSequent = createSideproofSequent(runningSequent, envTermBuilder, predicateParameterSorts, predicateParameterTerms, loopSpecs);

        // Initialise proofStarter for sideProof
        ProofStarter proofStarter = new ProofStarter(false);
        try {
            proofStarter.init(sideSequent, proofEnv, "Invariant Generation");
        } catch (ProofInputException ex) {
            //TODO: Solve gracefully
            throw new RuntimeException(ex);
        }

        Proof sideProof = proofStarter.getProof();
        Services sideServices = sideProof.getServices();

        // Add the loop specifications to the repository s.t. KeY can use the invariants for the specified loops
        for (LoopSpecification loopSpec: loopSpecs) {
            sideServices.getSpecificationRepository().addLoopInvariant(loopSpec);
        }

        prepareProof(proofStarter, sideProof);

        ProofSearchInformation<Proof, Goal> pi = proofStarter.start();

        ImmutableList<Goal> openGoals = pi.getProof().openGoals();

        for(int goalIndex = 0; goalIndex < openGoals.size(); goalIndex++) {
            System.out.printf("Goal %d ------------------------------------------------------%n", goalIndex);
            System.out.println(ProofSaver.printAnything(openGoals.get(goalIndex).node().sequent(), sideServices));
        }

        //get goals into a digestible form

        return new JTerm[0];
    }

    private LocationVariable[] collectAllProgramVariables(Sequent sequent) {
        Set<LocationVariable> locationVariableSet = new HashSet<>();

        //Collect all programm variables, as we need it for the fresh invariant
        for (SequentFormula sf: sequent.asList()) {
            TermProgramVariableCollector pvc = new TermProgramVariableCollector(services);
            sf.formula().execPostOrder(pvc);
            locationVariableSet.addAll(pvc.result());
        }

        return locationVariableSet.toArray(new LocationVariable[0]);
    }

    private Sequent createSideproofSequent(Sequent sequent, TermBuilder envTermBuilder, Sort[] predicateParameterSorts,
                                           JTerm[] predicateParameterTerms, List<LoopSpecification> loopSpecs) {
        Sequent sideSequent = JavaDLSequentKit.createAnteSequent(sequent.antecedent().asList());

        for (SequentFormula sf: sequent.succedent()) {
            Term fml = sf.formula();
            SequentFormula sfToAdd = sf;
            //goBelowUpdates returns a pair of updates and what is below updates
            var updateTermPair = TermBuilder.goBelowUpdates2((JTerm) fml);
            JavaBlock termJavaBlock = updateTermPair.second.javaBlock();
            if (!termJavaBlock.isEmpty()) {
                var activeStatement = JavaTools.getActiveStatement(termJavaBlock);
                if (activeStatement instanceof While) {
                    JFunction placeholderInvariant = new JFunction(
                            new Name(envTermBuilder.newName("freshInv")),
                            JavaDLTheory.FORMULA,
                            predicateParameterSorts
                    );

                    JTerm uninterpretedInvariantFunction = envTermBuilder.func(placeholderInvariant, predicateParameterTerms);

                    var invariantFormula = envTermBuilder.prog(
                            ((JModality) updateTermPair.second.op()).kind(),
                            termJavaBlock,
                            uninterpretedInvariantFunction
                    );

                    invariantFormula = envTermBuilder.applySequential(updateTermPair.first, invariantFormula);

                    BasicLoopSpecificationImpl loopSpec = new BasicLoopSpecificationImpl((While) activeStatement,
                            uninterpretedInvariantFunction,
                            envTermBuilder.allLocs());
                    loopSpecs.add(loopSpec);
                    sfToAdd = new SequentFormula(invariantFormula);
                }

            }
            sideSequent = sideSequent.addFormula(sfToAdd, false, true).sequent();

        }

        return sideSequent;
    }

    private void prepareProof(ProofStarter proofStarter, Proof sideProof) {
        JavaCardDLStrategyFactory strategyFactory = new JavaCardDLStrategyFactory();
        StrategyProperties properties = services.getProof().getSettings().getStrategySettings().getActiveStrategyProperties();
        properties.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_SCOPE_INV_TACLET);
        proofStarter.setStrategy(strategyFactory.create(sideProof, properties));
        proofStarter.setMaxRuleApplications(10000);
    }

}
