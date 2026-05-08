package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.util.loop_inv_generation.ILoopInvariantGenerator;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure.CandidateGenerationTask;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure.CandidateInvariant;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure.Conjunct;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.NamedVariableCollector;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Util;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.VerificationCondition;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

public class LoopInvariantGenerator implements ILoopInvariantGenerator {
    private final Services services;
    private static final SolverType CVC5_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("cvc5"))
            .findFirst().orElse(null);

    private final BlockingQueue<CandidateInvariant> taskQueue = new LinkedBlockingQueue<>();

    public LoopInvariantGenerator(Services services) {
        this.services = services;
    }

    @Override
    public Term generateLoopInvariant() {
        List<VerificationCondition> verificationConditions = Util.generateVerificationConditions(CVC5_SOLVER, services);
        Set<LocationVariable> changingVariables = Util.collectChangingVariables(services);
        AtomicBoolean isFinished = new AtomicBoolean(false);
        AtomicReference<Term> loopInvariant = new AtomicReference<>(null);
        Set<CandidateInvariant> traversedCandidates = ConcurrentHashMap.newKeySet();

        int threadCount = 1;

        // Create an ExecutorService with a cached thread pool
        ThreadPoolExecutor executorService = (ThreadPoolExecutor) Executors.newFixedThreadPool(threadCount);

        // Initialize the CandidateInvariant
//        taskQueue.add(new CandidateGenerationTask(services, isFinished, loopInvariant, taskQueue, traversedCandidates, testCandidate, verificationConditions));
        CandidateInvariant initialCandidate = new CandidateInvariant(services);
//        CandidateInvariant initialCandidate = generateTestCandidate(verificationConditions);
//        taskQueue.add(new CandidateGenerationTask(services, isFinished, loopInvariant, taskQueue, traversedCandidates, initialCandidate, verificationConditions));
        try {
            taskQueue.put(initialCandidate);
            for (int i = 0; i < threadCount; i++) {
                executorService.submit(new CandidateGenerationTask(services, isFinished, loopInvariant, taskQueue, traversedCandidates, verificationConditions, changingVariables, i+1));
            }
        } catch (InterruptedException e) {
            return loopInvariant.get();
        }

        while ((!taskQueue.isEmpty() || executorService.getActiveCount() > 0) && !isFinished.get()) {
            try {
                Thread.sleep(1000);
                System.err.println("Active threads: " + executorService.getActiveCount());
                System.err.println("Queue size: " + taskQueue.size());

            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }

        executorService.shutdown();
        try {
            if (!executorService.awaitTermination(10, TimeUnit.SECONDS)) {
                executorService.shutdownNow();
            }
        } catch (InterruptedException e) {
            executorService.shutdownNow();
        }

        return loopInvariant.get();
    }

    private CandidateInvariant generateTestCandidate(List<VerificationCondition> verificationConditions) {

        String[] names = new String[]{"fromIndex", "toIndex", "array", "idx", "value"};

        Map<String, Term> terms = extractAllVariables(List.of(names), verificationConditions);
        Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();

        TermBuilder tb = services.getTermBuilder();
        JTerm fromTerm = (JTerm) terms.get("fromIndex");
        JTerm toTerm = (JTerm) terms.get("toIndex");
        JTerm idxTerm = (JTerm) terms.get("idx");
        JTerm valueTerm = (JTerm) terms.get("value");
        JTerm arrayTerm = (JTerm) terms.get("array");
        Term term1 = tb.geq(fromTerm, idxTerm);
        Term term2 = tb.geq(tb.sub(idxTerm, tb.one()), toTerm);

        LogicVariable iVar = new LogicVariable(new Name("i"), intSort);
        JTerm iTerm = tb.var(iVar);
        JTerm restrictor = tb.and(tb.leq(fromTerm, iTerm),
                tb.leq(iTerm, tb.sub(idxTerm, tb.one())));
        JTerm scopus = tb.equals(tb.select(intSort, services.getTermBuilder().getBaseHeap(), arrayTerm, tb.arr(iTerm)),
                valueTerm);
        Term term6 = tb.all(iVar, tb.imp(restrictor, scopus));



        CandidateInvariant candidate = new CandidateInvariant(services);
        candidate.addConjunct(term1, Conjunct.create(term1, services));
        candidate.addConjunct(term2, Conjunct.create(term2, services));
//        candidate.addConjunct(term3, Conjunct.create(term3, services));
//        candidate.addConjunct(term4, Conjunct.create(term4, services));
//        candidate.addConjunct(term5, Conjunct.create(term5, services));
        candidate.addConjunct(term6, Conjunct.create(term6, services));
        return candidate;
    }

    private Map<String, Term> extractAllVariables(List<String> names, List<VerificationCondition> verificationConditions) {
        NamedVariableCollector nvc = new NamedVariableCollector(names);

        for (VerificationCondition vc : verificationConditions) {
            var formulas = new ArrayList<>(vc.getSequent().antecedent().asList().stream().toList());
            formulas.addAll(vc.getSequent().succedent().asList().stream().toList());
            formulas.forEach(f -> f.formula().execPostOrder(nvc));
        }

        return nvc.result();
    }


}
