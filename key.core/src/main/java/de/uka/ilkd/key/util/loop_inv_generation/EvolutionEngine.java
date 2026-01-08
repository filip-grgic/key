package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.mutations.Mutation;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantGen;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.Pair;

import java.util.*;

public class EvolutionEngine {

    private Services services;
    private Term[] termPool;
    private Sequent[] verificationConditions;
    private EvolutionEngineParameters parameters;

    private List<LoopInvariantFreeGenome> population;
    private LoopInvariantFreeGenome solution;

    public EvolutionEngine(Services services, Term[] termPool, Sequent[] verificationConditions,
                           EvolutionEngineParameters parameters) {
        this.services = services;
        this.termPool = termPool;
        this.verificationConditions = verificationConditions;
        this.parameters = parameters;
        parameters.setTermPool(termPool);

        this.population = new ArrayList<>();
    }

    public LoopInvariantFreeGenome getSolution() {
        return solution;
    }

    public void launch() {

        int generations = this.parameters.getGenerations();
        init();
        evaluate();

        while (generations != 0 && solution == null) {

            //Selection Phase:
            List<Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome>> pairs = select();

            //Recombination Phase:
            List<LoopInvariantFreeGenome> children = recombine(pairs);

            //Mutation Phase:
            mutate(children);

            //Replacement Phase:
            replace(children);

            //Evaluation
            evaluate();
            if (solution != null) {
                break;
            }

            //If generations is negative, the loop is infinite until a solution is found
            if (generations > 0) {
                generations -= 1;
            }
        }

    }

    private void init() {
        Random random = new Random();

        while (population.size() < this.parameters.getPopulationSize()) {
            int randomTermIndex = random.nextInt(termPool.length);
            LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, termPool[randomTermIndex]);

            List<LoopInvariantFreeGen> conjunct = new ArrayList<>();
            conjunct.add(gen);

            LoopInvariantFreeGenome genome = new LoopInvariantFreeGenome(services);
            genome.addConjunct(conjunct);

            population.add(genome);
        }
    }

    private void evaluate() {

        //Evaluation Phase: Check score of each individual in the population
        for (LoopInvariantFreeGenome individual: population) {
            individual.checkFitness();
            if (individual.isSolution()) {
                solution = individual;
                break;
            }
        }

        population.sort(LoopInvariantFreeGenome.getComparator());
    }

    private List<Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome>> select() {

        double overallFitness = 0;
        double[] probabilities = new double[population.size()];
        List<Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome>> pairs = new ArrayList<>();
        Random random = new Random();

        for (LoopInvariantFreeGenome individual: population) {
            overallFitness += individual.getFitness();
        }

        probabilities[0] = population.getFirst().getFitness()/overallFitness;
        probabilities[population.size()] = 1.0;

        for (int i = 1; i < population.size() - 1; i++) {
            probabilities[i] = population.get(i-1).getFitness()/overallFitness + probabilities[i-1];
        }

        for (int i = 0; i <= parameters.getPopulationSize()*parameters.getReplacementRate(); i++) {
            int parent1Index = Arrays.binarySearch(probabilities, random.nextDouble());
            //Necessary because of how the binary search method works; convert the insertion point to the correct index
            if (parent1Index < 0) {
                parent1Index = -parent1Index - 1;
            }
            int parent2Index = parent1Index;

            while (parent2Index == parent1Index) {
                parent2Index = Arrays.binarySearch(probabilities, random.nextDouble());
                if (parent2Index < 0) {
                    parent2Index = -parent2Index - 1;
                }
            }

            pairs.add(new Pair<>(population.get(parent1Index), population.get(parent2Index)));
        }

        return pairs;
    }

    private List<LoopInvariantFreeGenome> recombine(List<Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome>> parentPairs) {
        List<LoopInvariantFreeGenome> children = new ArrayList<>();
        for (Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome> parentPair: parentPairs) {
            children.add(parentPair.first.combine(parentPair.second));
        }
        return children;
    }

    private void mutate(List<LoopInvariantFreeGenome> children) {
        Random random = new Random();
        List<Mutation> mutations = parameters.getMutations();
        for (LoopInvariantFreeGenome child: children) {
            Mutation mutation = null;
            for (int i = 0; i < mutations.size() && (mutation == null || !(mutation.suitableForMutation(child))); i++) {
                mutation = mutations.get(random.nextInt(mutations.size()));
            }

            mutation.mutate(child);
        }

    }

    private void replace(List<LoopInvariantFreeGenome> mutatedChildren) {
        population.addAll(mutatedChildren);
        population.sort(LoopInvariantFreeGenome.getComparator());
        population = population.subList(0, parameters.getPopulationSize());
    }
}
