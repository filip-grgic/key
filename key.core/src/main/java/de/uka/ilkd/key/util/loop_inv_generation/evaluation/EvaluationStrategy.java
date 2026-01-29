package de.uka.ilkd.key.util.loop_inv_generation.evaluation;

import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;

import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

public class EvaluationStrategy extends AbstractEvaluationStrategy {

    private int threadPoolSize;
    private LoopInvariantFreeGenome solution = null;

    public EvaluationStrategy(int threadPoolSize) {
        super(threadPoolSize);
    }

    @Override
    public void evaluate(List<LoopInvariantFreeGenome> genomeList) {
        ThreadPoolExecutor executor = (ThreadPoolExecutor) Executors.newFixedThreadPool(threadPoolSize);
        for (LoopInvariantFreeGenome individual : genomeList) {
            executor.submit(new EvaluationWorker(individual));
        }

        while (!executor.getQueue().isEmpty() || executor.getActiveCount() > 0) {
//            System.out.printf("queue size: %s, active threads: %s\n", executor.getQueue().size(), executor.getActiveCount());
            try {
                Thread.sleep(1000);
            } catch (InterruptedException e) {
                executor.shutdownNow();
                throw new RuntimeException(e);
            }
        }

        executor.close();

        //Evaluation Phase: Check score of each individual in the population
        for (LoopInvariantFreeGenome individual : genomeList) {
            if (individual.isSolution()) {
                solution = individual;
                break;
            }
        }

    }

    @Override
    public boolean hasSolution() {
        return solution != null;
    }

    @Override
    public LoopInvariantFreeGenome getSolution() {
        return solution;
    }

    public void setThreadPoolSize(int threadPoolSize) {
        this.threadPoolSize = threadPoolSize;
    }

    private static class EvaluationWorker implements Runnable {

        private final LoopInvariantFreeGenome genome;

        EvaluationWorker(LoopInvariantFreeGenome genome) {
            this.genome = genome;
        }

        @Override
        public void run() {
            genome.checkFitness();
        }
    }
}
