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

    private final BlockingQueue<CandidateGenerationTask> taskQueue = new LinkedBlockingQueue<>();

    public LoopInvariantGenerator(Services services) {
        this.services = services;
    }

    @Override
    public Term generateLoopInvariant() {
        List<VerificationCondition> verificationConditions = Util.generateVerificationConditions(CVC5_SOLVER, services);
        AtomicBoolean isFinished = new AtomicBoolean(false);
        AtomicReference<Term> loopInvariant = new AtomicReference<>(null);
        Set<CandidateInvariant> traversedCandidates = ConcurrentHashMap.newKeySet();

        CandidateInvariant testCandidate = generateTestCandidate(verificationConditions);
        taskQueue.add(new CandidateGenerationTask(services, isFinished, loopInvariant, taskQueue, traversedCandidates, testCandidate, verificationConditions));

        // Create an ExecutorService with a cached thread pool
        ThreadPoolExecutor executorService = (ThreadPoolExecutor) Executors.newFixedThreadPool(4);

        // Initialize the CandidateInvariant
//        CandidateInvariant initialCandidate = new CandidateInvariant(services);
//        taskQueue.add(new CandidateGenerationTask(services, isFinished, loopInvariant, taskQueue, traversedCandidates, initialCandidate, verificationConditions));

        int i = 0;
        while ((!taskQueue.isEmpty() || executorService.getActiveCount() > 0) && !isFinished.get()) {
            while (taskQueue.peek() != null) {
                executorService.submit(taskQueue.poll());
            }

            try {
                Thread.sleep(100);

                if (i == 0) {
                    System.err.println("Active threads: " + executorService.getActiveCount());
                    System.err.println("Queue size: " + taskQueue.size());
                }

                i = (i + 1) % 10;

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

        String[] names = new String[]{"i", "j", "array", "pattern"};

        Map<String, Term> terms = extractAllVariables(List.of(names), verificationConditions);
        Sort intSort = services.getTypeConverter().getIntegerLDT().targetSort();

        TermBuilder tb = services.getTermBuilder();
        JTerm iTerm = (JTerm) terms.get("i");
        JTerm jTerm = (JTerm) terms.get("j");
        JTerm arrayTerm = (JTerm) terms.get("array");
        JTerm patternTerm = (JTerm) terms.get("pattern");
        Term term1 = tb.geq(iTerm, tb.zero());
        Term term2 = tb.geq(jTerm, tb.zero());
        Term term3 = tb.lt(iTerm, tb.dotLength(arrayTerm));
        Term term4 = tb.leq(tb.add(iTerm, jTerm), tb.dotLength(arrayTerm));
        Term term5 = tb.leq(jTerm, tb.dotLength(patternTerm));

        LogicVariable xVar = new LogicVariable(new Name("x"), intSort);
        JTerm xTerm = tb.var(xVar);
        JTerm restrictor = tb.and(tb.leq(tb.zero(), xTerm),
                tb.lt(xTerm, jTerm),
                tb.lt(tb.add(iTerm, xTerm), tb.dotLength(arrayTerm)),
                tb.lt(xTerm, tb.dotLength(patternTerm)));
        JTerm scopus = tb.equals(tb.select(intSort, services.getTermBuilder().getBaseHeap(), arrayTerm, tb.arr(tb.add(iTerm, xTerm))),
                tb.select(intSort, services.getTermBuilder().getBaseHeap(), patternTerm, tb.arr(xTerm)));
        Term term6 = tb.all(xVar, tb.imp(restrictor, scopus));

        CandidateInvariant candidate = new CandidateInvariant(services);
//        candidate.addConjunct(term1, Conjunct.create(term1, services));
//        candidate.addConjunct(term2, Conjunct.create(term2, services));
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
