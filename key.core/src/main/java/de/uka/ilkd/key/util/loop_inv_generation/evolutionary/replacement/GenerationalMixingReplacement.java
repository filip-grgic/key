package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.replacement;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation.IEvaluationStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

public class GenerationalMixingReplacement extends AbstractReplacementStrategy {

    public GenerationalMixingReplacement(int populationSize, IEvaluationStrategy evaluationStrategy) {
        super(populationSize, evaluationStrategy);
    }

    @Override
    public List<LoopInvariantFreeGenome> replace(List<LoopInvariantFreeGenome> population, List<LoopInvariantFreeGenome> mutatedChildren) {
        List<LoopInvariantFreeGenome> result = new ArrayList<>();

        result.addAll(population);
        result.addAll(mutatedChildren);
        evaluationStrategy.evaluate(result);

        Collections.shuffle(result);

        result.sort(LoopInvariantFreeGenome.getComparator());
        return result.subList(0, populationSize);
    }
}
