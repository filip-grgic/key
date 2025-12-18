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
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
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
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class EvolutionaryLoopInvariantGenerator {

    private final Services services;
    private Term[] sequentTerms;
    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3"))
            .findFirst().orElse(null);

    public EvolutionaryLoopInvariantGenerator(Services services) {
        this.services = services;
    }

    public void generateLoopInvariant() {
//        ImmutableList<Goal> verificationConditions = generateVerificationConditions();

//        SMTProblem smtProblem = new SMTProblem(verificationConditions.get(0));


        /*
        Test the following SMT problem:
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (=> (and (= 3 (+ x y)) (= 2 x)) (= 1 y)))
        (check-sat)
        (exit)
         */
        TermBuilder tb = services.getTermBuilder();
        Sort integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
        LocationVariable x = tb.locationVariable("x", integerSort, true);
        LocationVariable y = tb.locationVariable("y", integerSort, true);
        JTerm xVar = tb.var(x);
        JTerm yVar = tb.var(y);
        Term antecedent1 = tb.equals(tb.add(xVar, yVar), tb.zTerm(3));
        Term antecedent2 = tb.equals(xVar, tb.zTerm(2));
        Term succedentTerm = tb.equals(yVar, tb.zTerm(1));

        ImmutableList<SequentFormula> antecedent = ImmutableList.of(new SequentFormula(antecedent1), new SequentFormula(antecedent2));
        ImmutableList<SequentFormula> succedent = ImmutableList.of(new SequentFormula(succedentTerm));

        Sequent sequent = JavaDLSequentKit.createSequent(antecedent, succedent);

        ProofEnvironment proofEnv = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
        ProofStarter proofStarter = new ProofStarter(false);
        try {
            proofStarter.init(sequent, proofEnv, "Invariant Generation");
        } catch (ProofInputException ex) {
            //TODO: Solve gracefully
            throw new RuntimeException(ex);
        }

        Proof sideProof = proofStarter.getProof();
        Services sideServices = sideProof.getServices();

        SMTProblem smtProblem = new SMTProblem(sequent, sideServices);
        SMTSettings settings = new DefaultSMTSettings(
                sideProof.getSettings().getSMTSettings(),
//                ProofDependentSMTSettings.getDefaultSettingsData(),
                ProofIndependentSMTSettings.getDefaultSettingsData(),
                new NewSMTTranslationSettings(),
                sideProof
        );
        SolverLauncher launcher = new SolverLauncher(settings);
        launcher.launch(smtProblem, sideServices, Z3_SOLVER);

        System.out.printf("SMT Problem result: %s%n", smtProblem.getFinalResult());


    }

    private ImmutableList<Goal> generateVerificationConditions() {
        ProofEnvironment proofEnv = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
        Services envServices = proofEnv.getServicesForEnvironment();
        TermBuilder envTermBuilder = envServices.getTermBuilder();
        Sequent runningSequent = services.getProof().openGoals().head().sequent();

        sequentTerms = collectAllTerms(runningSequent);

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

        //Verification Conditions are the open goals that are still left
        return pi.getProof().openGoals();
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

    private Term[] collectAllTerms(Sequent sequent) {
        Set<Term> termSet = new HashSet<>();

        for (SequentFormula sf: sequent.asList()) {
            TermCollector termCollector = new TermCollector();
            sf.formula().execPostOrder(termCollector);
            termSet.addAll(termCollector.result());
        }

        return termSet.toArray(new Term[0]);
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
