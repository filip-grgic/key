package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.speclang.BasicLoopSpecificationImpl;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
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

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public class Util {

    /**
     * Generates the verification conditions for the given proof by using a sideproof after inserting the fresh invariant
     * for the While loop in the sequent.
     * @param services the services of the proof.
     * @return the verification conditions for the proof.
     */
    public static List<VerificationCondition> generateVerificationConditions(Services services) {
        ProofEnvironment proofEnv = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
        Services envServices = proofEnv.getServicesForEnvironment();
        TermBuilder envTermBuilder = envServices.getTermBuilder();
        Sequent runningSequent = services.getProof().openGoals().head().sequent();

        // Get all program variables and extract their sorts for the fresh invariant
        LocationVariable[] locationVariables = collectAllProgramVariables(runningSequent, services);
        Sort[] predicateParameterSorts = new Sort[locationVariables.length];
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
            throw new RuntimeException(ex);
        }

        Proof sideProof = proofStarter.getProof();
        Services sideServices = sideProof.getServices();

        // Necessary as the class invariant axiom otherwise wouldn't be usable
        addPOTaclets(sideProof, services);

        // Add the loop specifications to the repository s.t. KeY can use the invariants for the specified loops
        for (LoopSpecification loopSpec : loopSpecs) {
            sideServices.getSpecificationRepository().addLoopInvariant(loopSpec);
        }

        prepareProof(proofStarter, sideProof, services);
        ProofSearchInformation<Proof, Goal> pi = proofStarter.start();
        ProofSaver ps = new ProofSaver(pi.getProof(), Paths.get("/home/filip/Desktop/doneProof"), true);
        ps.save();

        //Verification Conditions are the open goals that are still left
        return convertGoalsToVerificationConditions(pi.getProof().openGoals(), loopSpecs, services);
    }

    /**
     * Adds the class invariant axiom to the sideproof as a taclet.
     * @param sideProof the sideproof.
     * @param services the services of the proof.
     */
    private static void addPOTaclets(Proof sideProof, Services services) {
        FunctionalOperationContractPO po = new FunctionalOperationContractPO(sideProof.getInitConfig(), (FunctionalOperationContract) services.getSpecificationRepository().getContractPOForProof(services.getProof()).getContract());
        po.registerClassAxiomTaclets(po.getContainerType(), sideProof.getInitConfig());
        sideProof.getOpenGoal(sideProof.root()).indexOfTaclets().addTaclets(
                po.getInitialTaclets()
        );
    }

    /**
     * Converts the open goals of the sideproof to verification conditions.
     * @param goals the open goals of the sideproof.
     * @param loopSpecs the loop specifications of the sideproof.
     * @param services the services of the proof.
     * @return the verification conditions of the sideproof.
     */
    private static List<VerificationCondition> convertGoalsToVerificationConditions(ImmutableList<Goal> goals, List<LoopSpecification> loopSpecs, Services services) {
        List<VerificationCondition> result = new ArrayList<>();

        for (int i = 0; i < goals.size(); i++) {
            result.add(new VerificationCondition(services, goals.get(i).sequent(), loopSpecs.getFirst()));
        }

        return result;
    }

    /**
     * Collects all program variables in the sequent.
     * @param sequent the sequent.
     * @param services the services of the proof.
     * @return an array of all program variables in the sequent.
     */
    private static LocationVariable[] collectAllProgramVariables(Sequent sequent, Services services) {
        Set<LocationVariable> locationVariableSet = new HashSet<>();

        //Collect all program variables, as we need it for the fresh invariant
        for (SequentFormula sf : sequent.asList()) {
            TermProgramVariableCollector pvc = new TermProgramVariableCollector(services);
            sf.formula().execPostOrder(pvc);
            locationVariableSet.addAll(pvc.result());
        }

        locationVariableSet = locationVariableSet.stream().filter((locVar) ->
                locVar.sort() == services.getTypeConverter().getIntegerLDT().targetSort() ||
                        locVar.sort().toString().equals("int[]") ||
                        locVar.sort().equals(services.getTypeConverter().getHeapLDT().targetSort())
        ).collect(Collectors.toSet());

        return locationVariableSet.toArray(new LocationVariable[0]);
    }

    /**
     * Creates the sideproof sequent by adding a fresh invariant for the While loop in the sequent.
     * The sideproof will then try to prove the sequent using the fresh invariant.
     * @param sequent the sequent.
     * @param envTermBuilder the term builder of the proof environment.
     * @param predicateParameterSorts the sorts of the predicate parameters of the fresh invariant.
     * @param predicateParameterTerms the terms of the predicate parameters of the fresh invariant.
     * @param loopSpecs the loop specifications of the sideproof.
     * @return the sideproof sequent.
     */
    private static Sequent createSideproofSequent(Sequent sequent, TermBuilder envTermBuilder, Sort[] predicateParameterSorts,
                                           JTerm[] predicateParameterTerms, List<LoopSpecification> loopSpecs) {
        Sequent sideSequent = JavaDLSequentKit.createAnteSequent(sequent.antecedent().asList());

        for (SequentFormula sf : sequent.succedent()) {
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

                    BasicLoopSpecificationImpl loopSpec = new BasicLoopSpecificationImpl((While) activeStatement,
                            uninterpretedInvariantFunction,
                            envTermBuilder.allLocs());
                    loopSpecs.add(loopSpec);
                }

            }
            sideSequent = sideSequent.addFormula(sfToAdd, false, true).sequent();
        }

        return sideSequent;
    }

    /**
     * Prepares the properties needed for the sideproof.
     * @param proofStarter the proof starter.
     * @param sideProof the sideproof.
     * @param services the services of the proof.
     */
    private static void prepareProof(ProofStarter proofStarter, Proof sideProof, Services services) {
        JavaCardDLStrategyFactory strategyFactory = new JavaCardDLStrategyFactory();
        StrategyProperties properties = services.getProof().getSettings().getStrategySettings().getActiveStrategyProperties();
        properties.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_SCOPE_INV_TACLET);
        properties.setProperty(StrategyProperties.SKOLEM_OPTIONS_KEY, StrategyProperties.SKOLEM_OFF);
        proofStarter.setStrategy(strategyFactory.create(sideProof, properties));
        proofStarter.setMaxRuleApplications(10000);
    }

}
