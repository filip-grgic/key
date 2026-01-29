package de.uka.ilkd.key.util.loop_inv_generation.evaluation;

public abstract class AbstractEvaluationStrategy implements IEvaluationStrategy {

    private int threadPoolSize;

    protected AbstractEvaluationStrategy(int threadPoolSize) {
        this.threadPoolSize = threadPoolSize;
    }

    public void setThreadPoolSize(int threadPoolSize) {
        this.threadPoolSize = threadPoolSize;
    }
}
