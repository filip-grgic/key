package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.replacement;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation.IEvaluationStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

public class MixingWithImmigrationReplacement extends AbstractReplacementStrategy {

    private final Services services;
    private final EvolutionEngineParameters parameters;
    // The percentage that should come from the better half
    double elitistRate;
    // The percentage that should come from the worse half
    double unfitRate;

    public MixingWithImmigrationReplacement(double elitistRate,
                                            double unfitRate,
                                            EvolutionEngineParameters parameters,
                                            Services services,
                                            IEvaluationStrategy evaluationStrategy) {
        super(parameters.getPopulationSize(), evaluationStrategy);
        assert elitistRate + unfitRate <= 1.0;

        this.elitistRate = elitistRate;
        this.unfitRate = unfitRate;
        this.services = services;
        this.parameters = parameters;
    }

    @Override
    public List<LoopInvariantFreeGenome> replace(List<LoopInvariantFreeGenome> population, List<LoopInvariantFreeGenome> mutatedChildren) {

        Random random = new Random();
        List<LoopInvariantFreeGenome> interimPopulation = new ArrayList<>(population);
        interimPopulation.addAll(mutatedChildren);
        evaluationStrategy.evaluate(interimPopulation);
        List<LoopInvariantFreeGenome> eliteHalf = new ArrayList<>(interimPopulation.subList(0, interimPopulation.size() / 2));
        List<LoopInvariantFreeGenome> worseHalf = new ArrayList<>(interimPopulation.subList(eliteHalf.size(), interimPopulation.size()));

        List<LoopInvariantFreeGenome> result = new ArrayList<>();

        //Needed to avoid ConcurrentModificationException
//        int eliteHalfSize = eliteHalf.size();
        while (result.size() < populationSize*elitistRate) {
            int index = random.nextInt(eliteHalf.size());
            result.add(eliteHalf.remove(index));
//            eliteHalfSize--;
        }

//        int worseHalfSize = worseHalf.size();
        while (result.size() < populationSize*(elitistRate + unfitRate)) {
            int index = random.nextInt(worseHalf.size());
            result.add(worseHalf.remove(index));
//            worseHalfSize--;
        }

        while (result.size() < populationSize) {
            result.add(LoopInvariantFreeGenome.generateRandomGenome(parameters, services));
        }

        evaluationStrategy.evaluate(result);
        Collections.shuffle(result);
        result.sort(LoopInvariantFreeGenome.getComparator());

        return new ArrayList<>(result.subList(0, populationSize));

    }
}
