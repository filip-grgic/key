package de.uka.ilkd.key.util.loop_inv_generation.evolutionary;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.Assignment;
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
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.speclang.BasicLoopSpecificationImpl;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.strategy.JavaCardDLStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import de.uka.ilkd.key.util.loop_inv_generation.ILoopInvariantGenerator;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.VerificationCondition;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.visitors.EnsuresTermCollector;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.visitors.TermSortCollector;
import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.engine.ProofSearchInformation;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import java.util.*;
import java.util.stream.Collectors;

public class EvolutionaryLoopInvariantGenerator implements ILoopInvariantGenerator {

    private final Services services;
    private Term[] sequentTerms;
    private RandomAccessSet<LocationVariable> allVariables;
    private RandomAccessSet<LocationVariable> changingVariables;
    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3"))
            .findFirst().orElse(null);
    private static final SolverType CVC5_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("cvc5"))
            .findFirst().orElse(null);

    public EvolutionaryLoopInvariantGenerator(Services services) {
        this.services = services;
//        this.programVariableSet = new HashSet<>();
    }

    public Term generateLoopInvariant() {
        List<Term> postconditions = getPostconditions();

        VerificationCondition[] verificationConditions = generateVerificationConditions();

        var termSorts = collectTermSorts(verificationConditions);

        EvolutionEngineParameters engineParameters = new EvolutionEngineParameters(sequentTerms, allVariables,
                changingVariables, termSorts, services, verificationConditions, postconditions);
        engineParameters.setGenerations(40);
        engineParameters.setPopulationSize(20);
        engineParameters.setEvaluationThreads(5);

        EvolutionEngine engine = new EvolutionEngine(services, sequentTerms, engineParameters);
        engine.launch();

        if (engine.hasSolution()) {
            System.out.println("Found an invariant solution");
            System.out.println(engine.getSolution());
            return engine.getSolution().translateToTerm();
        } else {
            System.out.println("Did not find an invariant solution");
            return null;
        }
    }

    private List<Term> getPostconditions() {
        Term postcondition = services.getProof().root().sequent().succedent().getFirst().formula().sub(1).sub(1).sub(0);
        Queue<Term> processQueue = new ArrayDeque<>();
        processQueue.add(postcondition);

        List<Term> postconditions = new ArrayList<>();

        while (!processQueue.isEmpty()) {
            Term currentTerm = processQueue.poll();

            if (currentTerm.op().name().toString().equals("and")) {
                processQueue.add(currentTerm.sub(0));
                processQueue.add(currentTerm.sub(1));
            } else {
                postconditions.add(currentTerm);
            }
        }

        return filterPostconditions(postconditions);
    }

    private List<Term> filterPostconditions(List<Term> postconditions) {
        List<Term> result = new ArrayList<>();

        for (Term postcondition : postconditions) {
            if (!containsForbiddenSort(postcondition)) {
                result.add(postcondition);
            }
        }

        return result;
    }

    private boolean containsForbiddenSort(Term term) {
        if (term.sort().equals(services.getTypeConverter().getIntegerLDT().targetSort())) {
            return false;
        }

        if (!term.subs().isEmpty()) {
            for (Term sub : term.subs()) {
                if (containsForbiddenSort(sub)) {
                    return true;
                }
            }
        } else {
            return !term.sort().equals(services.getTypeConverter().getIntegerLDT().targetSort());
        }

        return false;
    }

    private VerificationCondition[] generateVerificationConditions() {
        ProofEnvironment proofEnv = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
        Services envServices = proofEnv.getServicesForEnvironment();
        TermBuilder envTermBuilder = envServices.getTermBuilder();
        Sequent runningSequent = services.getProof().openGoals().head().sequent();

        sequentTerms = collectAllTerms(runningSequent);

        // Get all program variables and extract their sorts for the fresh invariant
        LocationVariable[] locationVariables = collectAllProgramVariables(runningSequent);
//        programVariableSet = new HashSet<>(List.of(locationVariables));
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
            //TODO: Solve gracefully
            throw new RuntimeException(ex);
        }

        Proof sideProof = proofStarter.getProof();
        Services sideServices = sideProof.getServices();
        // Necessary as the class invariant axiom otherwise wouldn't be usable
        addPOTaclets(sideProof);

        // Add the loop specifications to the repository s.t. KeY can use the invariants for the specified loops
        for (LoopSpecification loopSpec : loopSpecs) {
            sideServices.getSpecificationRepository().addLoopInvariant(loopSpec);
        }

        prepareProof(proofStarter, sideProof);
        ProofSearchInformation<Proof, Goal> pi = proofStarter.start();

        //Verification Conditions are the open goals that are still left
        return convertGoalsToVerificationConditions(pi.getProof().openGoals(), loopSpecs);
    }

    private void addPOTaclets(Proof sideProof) {
        FunctionalOperationContractPO po = new FunctionalOperationContractPO(sideProof.getInitConfig(), (FunctionalOperationContract) services.getSpecificationRepository().getContractPOForProof(services.getProof()).getContract());
        po.registerClassAxiomTaclets(po.getContainerType(), sideProof.getInitConfig());
        sideProof.getOpenGoal(sideProof.root()).indexOfTaclets().addTaclets(
                po.getInitialTaclets()
        );
    }

    private VerificationCondition[] convertGoalsToVerificationConditions(ImmutableList<Goal> goals, List<LoopSpecification> loopSpecs) {
        VerificationCondition[] result = new VerificationCondition[goals.size()];

        for (int i = 0; i < goals.size(); i++) {
            //TODO: Implement for multiple possible loop specifications
            result[i] = new VerificationCondition(services, goals.get(i).sequent(), loopSpecs.getFirst(), CVC5_SOLVER);
        }

        return result;
    }

    private LocationVariable[] collectAllProgramVariables(Sequent sequent) {
        Set<LocationVariable> locationVariableSet = new HashSet<>();

        //Collect all program variables, as we need it for the fresh invariant
        for (SequentFormula sf : sequent.asList()) {
            TermProgramVariableCollector pvc = new TermProgramVariableCollector(services);
            sf.formula().execPostOrder(pvc);
            locationVariableSet.addAll(pvc.result());
        }

        //TODO: Implement for other types than integer as well
        locationVariableSet = locationVariableSet.stream().filter((locVar) ->
                locVar.sort() == services.getTypeConverter().getIntegerLDT().targetSort()
        ).collect(Collectors.toSet());

        return locationVariableSet.toArray(new LocationVariable[0]);
    }

    private Term[] collectAllTerms(Sequent sequent) {
        Set<Term> termSet = new HashSet<>();

        for (SequentFormula sf : sequent.asList()) {
            EnsuresTermCollector termCollector = new EnsuresTermCollector(services);
            sf.formula().execPostOrder(termCollector);
            termSet.addAll(termCollector.result());
        }

        return termSet.toArray(new Term[0]);
    }

    private Map<Sort, RandomAccessSet<Term>> collectTermSorts(Sequent sequent) {
        Map<Sort, RandomAccessSet<Term>> sortMap = new HashMap<>();

        for (SequentFormula sf : sequent.asList()) {
            TermSortCollector termSortCollector = new TermSortCollector(services);
            sf.formula().execPostOrder(termSortCollector);
            termSortCollector.result().forEach((key, value) -> {
                if (!sortMap.containsKey(key)) {
                    sortMap.put(key, new RandomAccessSet<>());
                }
                sortMap.get(key).addAll(value);
            });
        }

        return sortMap;
    }

    private Map<Sort, RandomAccessSet<Term>> collectTermSorts(VerificationCondition[] verificationConditions) {
        Map<Sort, RandomAccessSet<Term>> sortMap = new HashMap<>();
        for (VerificationCondition verificationCondition : verificationConditions) {
            collectTermSorts(verificationCondition.getSequent()).forEach((key, value) -> {
                if (!sortMap.containsKey(key)) {
                    sortMap.put(key, new RandomAccessSet<>());
                }
                sortMap.get(key).addAll(value);
            });
        }
        return sortMap;
    }

    private Sequent createSideproofSequent(Sequent sequent, TermBuilder envTermBuilder, Sort[] predicateParameterSorts,
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

                    allVariables = new RandomAccessSet<>();
                    changingVariables = new RandomAccessSet<>();

                    extractVariables((While) activeStatement, allVariables, changingVariables);

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

    private void extractVariables(While activeStatement, Set<LocationVariable> allVariables, Set<LocationVariable> changingVariables) {
        extractVariablesWithCursor(activeStatement.getBody(), allVariables, changingVariables);
        extractVariablesWithCursor(activeStatement.getGuard(), allVariables, changingVariables);
    }

    private void extractVariablesWithCursor(SyntaxElement element, Set<LocationVariable> allVariables, Set<LocationVariable> changingVariables) {
        SyntaxElementCursor cursor = element.getCursor();

        while (cursor.hasNext()) {
            SyntaxElement currentElement = cursor.getCurrentNode();

            if (currentElement instanceof LocationVariable) {
                allVariables.add((LocationVariable) currentElement);
            }

            if (currentElement instanceof Assignment) {
                if (currentElement.getChild(0) instanceof LocationVariable) {
                    changingVariables.add((LocationVariable) currentElement.getChild(0));
                }
            }

            if (!cursor.goToNext()) {
                break;
            }
        }
    }

    private void prepareProof(ProofStarter proofStarter, Proof sideProof) {
        JavaCardDLStrategyFactory strategyFactory = new JavaCardDLStrategyFactory();
        StrategyProperties properties = services.getProof().getSettings().getStrategySettings().getActiveStrategyProperties();
        properties.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, StrategyProperties.LOOP_SCOPE_INV_TACLET);
        proofStarter.setStrategy(strategyFactory.create(sideProof, properties));
        proofStarter.setMaxRuleApplications(10000);
    }

}
