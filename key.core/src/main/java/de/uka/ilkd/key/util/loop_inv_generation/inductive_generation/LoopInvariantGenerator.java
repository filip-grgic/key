package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.util.loop_inv_generation.ILoopInvariantGenerator;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure.CandidateGenerationTask;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure.CandidateInvariant;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Util;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.VerificationCondition;
import org.key_project.logic.Term;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

public class LoopInvariantGenerator implements ILoopInvariantGenerator {
    private final Services services;
    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3"))
            .findFirst().orElse(null);
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

        // Create an ExecutorService with a cached thread pool
        ThreadPoolExecutor executorService = (ThreadPoolExecutor) Executors.newFixedThreadPool(1);

        // Initialize the CandidateInvariant
        CandidateInvariant initialCandidate = new CandidateInvariant(services);
        taskQueue.add(new CandidateGenerationTask(services, isFinished, loopInvariant, taskQueue, initialCandidate, verificationConditions));
        
        while ((!taskQueue.isEmpty() || executorService.getActiveCount() > 0) && !isFinished.get()) {
            if (taskQueue.peek() != null) {
                executorService.submit(taskQueue.poll());
            }

            try {
                Thread.sleep(100);
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


}
