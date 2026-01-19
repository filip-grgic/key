package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.mutations.Mutation;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.structures.VerificationCondition;
import de.uka.ilkd.key.util.loop_inv_generation.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.util.collection.Pair;

import java.util.*;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;
import java.util.concurrent.TimeUnit;

public class EvolutionEngine {

    private final Services services;
    private final Term[] termPool;
    private final VerificationCondition[] verificationConditions;
    private final EvolutionEngineParameters parameters;

    private List<LoopInvariantFreeGenome> population;
    private LoopInvariantFreeGenome solution;

    public EvolutionEngine(Services services, Term[] termPool, VerificationCondition[] verificationConditions,
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

    public boolean hasSolution() {
        return solution != null;
    }

    public void launch() {

        System.out.println("Launching evolution engine...");

        int generations = this.parameters.getGenerations();
        init();
        evaluate();

        System.out.println("Successfully initialised evolution engine.");
        System.out.println("The evaluation resulted to the following fitness scores:");
        for (LoopInvariantFreeGenome genome : population) {
            System.out.println(genome.getFitness());
        }

        while (generations != 0 && solution == null) {

            System.out.printf("Generation #%d: highest score: %f\n", this.parameters.getGenerations() - generations,
                    population.getFirst().getFitness());

            //Selection Phase:
            List<Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome>> pairs = select();
            System.out.println("Successfully performed the selection phase.");

            //Recombination Phase:
            List<LoopInvariantFreeGenome> children = recombine(pairs);
            System.out.println("Successfully performed the recombination phase.");

            //Mutation Phase:
            mutate(children);
            System.out.println("Successfully performed the mutation phase.");

            //Replacement Phase:
            replace(children);
            System.out.println("Successfully performed the replacement phase.");

            //Evaluation
            evaluate();
            if (solution != null) {
                System.out.println("Found a solution! Aborting the process.");
                break;
            }

            //If generations is negative, the loop is infinite until a solution is found
            if (generations > 0) {
                generations -= 1;
            }
        }

    }

    /**
     * Initialises the evolution engine by generating a random population of the size as specified in
     * {@code this.parameters}.
     */
    private void init() {
        Random random = new Random();

        while (population.size() < this.parameters.getPopulationSize()) {
            int randomTermIndex = random.nextInt(termPool.length);
            LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, termPool[randomTermIndex]);

            RandomAccessSet<LoopInvariantFreeGen> conjunct = new RandomAccessSet<>();
            conjunct.add(gen);

            LoopInvariantFreeGenome genome = new LoopInvariantFreeGenome(services, verificationConditions);
            genome.addConjunct(conjunct);

            population.add(genome);
        }
    }

    /**
     * The fitness score of each genome in the population is updated and sorted according to their current fitness
     * scores. If any of these genomes is a possible solution, the evaluation phase will be aborted and the solution
     * will be saved into {@code solution}.
     */
    private void evaluate() {
        ThreadPoolExecutor executor = (ThreadPoolExecutor) Executors.newFixedThreadPool(4);
        for (LoopInvariantFreeGenome individual : population) {
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
        for (LoopInvariantFreeGenome individual : population) {
            if (individual.isSolution()) {
                solution = individual;
                break;
            }
        }

        population.sort(LoopInvariantFreeGenome.getComparator());
    }

    /**
     * Performs the selection phase where it is decided which genomes should be paired together. Currently, this is
     * decided by fitness scores, where genomes that have a higher fitness score are more likely to be part of a pair.
     *
     * @return a list of selection pairs
     */
    private List<Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome>> select() {

        double overallFitness = 0;
        double[] probabilities = new double[population.size()];
        List<Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome>> pairs = new ArrayList<>();
        Random random = new Random();

        for (LoopInvariantFreeGenome individual : population) {
            overallFitness += individual.getFitness();
        }

        probabilities[0] = population.getFirst().getFitness() / overallFitness;
        probabilities[population.size() - 1] = 1.0;

        for (int i = 1; i < population.size() - 1; i++) {
            probabilities[i] = population.get(i - 1).getFitness() / overallFitness + probabilities[i - 1];
        }

        for (int i = 0; i <= parameters.getPopulationSize() * parameters.getReplacementRate(); i++) {
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

    /**
     * Performs the recombination phase. The provided selection pairs are iterated through and combined according to the
     * genome's combination strategy. The resulting genomes ("children") are collected into a list and returned.
     *
     * @param parentPairs The selection pairs that were collected during the selection phase.
     * @return The combined children according to the provided selection pairs.
     */
    private List<LoopInvariantFreeGenome> recombine(List<Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome>> parentPairs) {
        List<LoopInvariantFreeGenome> children = new ArrayList<>();
        for (Pair<LoopInvariantFreeGenome, LoopInvariantFreeGenome> parentPair : parentPairs) {
            children.add(parentPair.first.combine(parentPair.second));
        }
        return children;
    }

    /**
     * Performs the mutation phase. All children that are the result of selection are mutated randomly through the
     * mutations as provided in the settings. It should be guaranteed that there is some mutation that can be performed
     * on every child, as otherwise the child won't be mutated at all.
     *
     * @param children that should be mutated
     */
    private void mutate(List<LoopInvariantFreeGenome> children) {
        Random random = new Random();
        List<Mutation> mutations = parameters.getMutations();
        List<Integer> probabilities = parameters.getMutationProbabilities();

        for (LoopInvariantFreeGenome child : children) {
            List<Mutation> possibleMutations = new ArrayList<>(mutations);
            List<Integer> possibleMutationsProbabilities = new ArrayList<>(probabilities);
            Mutation mutation = null;

            while (!possibleMutations.isEmpty()) {
                int index = Collections.binarySearch(possibleMutationsProbabilities, random.nextInt(possibleMutationsProbabilities.getLast()));
                if (index < 0) {
                    index = -index - 1;
                }

                Mutation potentialMutation = mutations.get(index);
                if (potentialMutation.suitableForMutation(child)) {
                    mutation = potentialMutation;
                    break;
                } else {
                    possibleMutations.remove(index);
                    int probUpdate = (index > 0) ? possibleMutationsProbabilities.get(index-1) : 0;
                    probUpdate = possibleMutationsProbabilities.get(index) - probUpdate;
                    List<Integer> probsPrefix = new ArrayList<>(possibleMutationsProbabilities.subList(0, index));
                    for (int i = index + 1; i < possibleMutationsProbabilities.size(); i++) {
                        probsPrefix.add(possibleMutationsProbabilities.get(i) - probUpdate);
                    }
                    possibleMutationsProbabilities = probsPrefix;
                }
            }

            if (mutation != null) {
                mutation.mutate(child);
            }
        }

    }

    /**
     * Performs the replacement phase. Adds the final children into the population, refreshes the fitness scores of all
     * population members and cuts off the genomes with the lowest scores, s.t. the new population arrives at the
     * specified size again.
     *
     * @param mutatedChildren the final children after the mutation phase.
     */
    private void replace(List<LoopInvariantFreeGenome> mutatedChildren) {
        population.addAll(mutatedChildren);
        evaluate();

//        for (LoopInvariantFreeGenome genome : population) {
//            genome.checkFitness();
//        }

        List<LoopInvariantFreeGenome> unshuffledPopulation = population;
        population = new ArrayList<>();
        Random random = new Random();

        while (!unshuffledPopulation.isEmpty()) {
            int index = random.nextInt(unshuffledPopulation.size());
            population.add(unshuffledPopulation.get(index));
            unshuffledPopulation.remove(index);
        }

        population.sort(LoopInvariantFreeGenome.getComparator());
        population = population.subList(0, parameters.getPopulationSize());
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
