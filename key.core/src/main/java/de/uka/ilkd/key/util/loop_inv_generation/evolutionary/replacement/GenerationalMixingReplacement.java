package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.replacement;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation.IEvaluationStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;

import java.util.ArrayList;
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

        List<LoopInvariantFreeGenome> unshuffledPopulation = result;
        result = new ArrayList<>();
        Random random = new Random();

        while (!unshuffledPopulation.isEmpty()) {
            int index = random.nextInt(unshuffledPopulation.size());
            result.add(unshuffledPopulation.get(index));
            unshuffledPopulation.remove(index);
        }

        result.sort(LoopInvariantFreeGenome.getComparator());
        return result.subList(0, populationSize);
    }
}
