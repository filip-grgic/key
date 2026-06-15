package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.util.loop_inv_generation.ILoopInvariantGenerator;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure.CandidateGenerationTask;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure.CandidateInvariant;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Tuple;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Util;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.VerificationCondition;
import org.key_project.logic.Term;

import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

public class LoopInvariantGenerator implements ILoopInvariantGenerator {
    private final Services services;
    private final BlockingQueue<CandidateInvariant> taskQueue = new LinkedBlockingQueue<>();

    public LoopInvariantGenerator(Services services) {
        this.services = services;
    }

    @Override
    public Term generateLoopInvariant() {
        List<VerificationCondition> verificationConditions = Util.generateVerificationConditions(services);
        AtomicBoolean isFinished = new AtomicBoolean(false);
        AtomicReference<Term> loopInvariant = new AtomicReference<>(null);
        Set<CandidateInvariant> traversedCandidates = ConcurrentHashMap.newKeySet();

        // Control how many threads are used for the generation
        int threadCount = 1;

        // Create an ExecutorService with a cached thread pool
        ThreadPoolExecutor executorService = (ThreadPoolExecutor) Executors.newFixedThreadPool(threadCount);

        // Initialise the CandidateInvariant
        generateInitialCandidates(verificationConditions);
        CandidateInvariant initialCandidate = new CandidateInvariant(services);
        try {
            taskQueue.put(initialCandidate);
            for (int i = 0; i < threadCount; i++) {
                executorService.submit(new CandidateGenerationTask(services, isFinished, loopInvariant, taskQueue, traversedCandidates, verificationConditions,i + 1));
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

    /**
     * Generate the initial candidates for the loop invariant generation using the verification conditions.
     * The initial candidates are generated using the updates on the placeholder invariant in the initiation VC
     * and then added automatically to the task queue.
     * @param verificationConditions
     */
    private void generateInitialCandidates(List<VerificationCondition> verificationConditions) {
        List<Tuple<Term,Term>> initUpdates = verificationConditions.stream().filter(v -> v.getVCKind().equals(VerificationCondition.VCKind.INITIATION))
                .toList().getFirst().getInitUpdates();

        List<List<Term>> initCombinations = generateInitCombinations(initUpdates, List.of(new ArrayList<>()));
        for (List<Term> combination : initCombinations) {
            CandidateInvariant candidate = new CandidateInvariant(services);
            for (Term term : combination) {
                candidate.addConjunct(new Tuple<>(term.sub(0), term.sub(1)), term);
            }
            taskQueue.add(candidate);
        }
    }

    /**
     * Generate all possible combinations of the initiation updates with the operators >=, <= and = in a recursive matter.
     *
     * @param initUpdates the updates on the placeholder invariant in the initiation VC
     * @param lists Keeps track of all the combinations so far
     * @return list of all possible combinations
     */
    private List<List<Term>> generateInitCombinations(List<Tuple<Term, Term>> initUpdates, List<List<Term>> lists) {
        List<List<Term>> result = new ArrayList<>();
        Tuple<Term, Term> first = initUpdates.getFirst();
        TermBuilder tb = services.getTermBuilder();

        for (List<Term> list : lists) {
            List<Term> newListGeq = new ArrayList<>(list);
            newListGeq.add(tb.geq((JTerm) first.first(), (JTerm) first.second()));
            result.add(newListGeq);

            List<Term> newListLeq = new ArrayList<>(list);
            newListLeq.add(tb.leq((JTerm) first.first(), (JTerm) first.second()));
            result.add(newListLeq);

            List<Term> newListEquals = new ArrayList<>(list);
            newListEquals.add(tb.equals((JTerm) first.first(), (JTerm) first.second()));
            result.add(newListEquals);
        }

        if (initUpdates.size() <= 1) {
            return result;
        }

        return generateInitCombinations(initUpdates.subList(1, initUpdates.size()), result);
    }

}
