package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.replacement;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation.IEvaluationStrategy;

public abstract class AbstractReplacementStrategy implements IReplacementStrategy {

    protected int populationSize;
    protected final IEvaluationStrategy evaluationStrategy;

    protected AbstractReplacementStrategy(int populationSize, IEvaluationStrategy evaluationStrategy) {
        this.populationSize = populationSize;
        this.evaluationStrategy = evaluationStrategy;
    }

    public void setPopulationSize(int populationSize) {
        this.populationSize = populationSize;
    }

}
