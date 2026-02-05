package de.uka.ilkd.key.util.loop_inv_generation.evolutionary;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation.AbstractEvaluationStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation.EvaluationStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations.*;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.replacement.AbstractReplacementStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.replacement.GenerationalMixingReplacement;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.*;

public class EvolutionEngineParameters {

    //Negative amount of generations signals infinite amounts
    private int generations = -1;
    private int populationSize = 10;
    private double replacementRate = 0.5;
    private int evaluationThreads = 4;
    private final List<Mutation> mutations = new ArrayList<>();
    private final List<Integer> mutationProbabilities = new ArrayList<>();
    private final AbstractEvaluationStrategy evaluationStrategy = new EvaluationStrategy(evaluationThreads);
    private final AbstractReplacementStrategy replacementStrategy = new GenerationalMixingReplacement(populationSize, evaluationStrategy);
    private Term[] termPool;
//    private final Set<LocationVariable> programVariableSet;
    protected final Map<Sort, RandomAccessSet<Term>> termSortSet;
    private final Services services;

    public EvolutionEngineParameters(Term[] termPool, Map<Sort, RandomAccessSet<Term>> termSortSet, Services services) {
        this.termPool = termPool;
        this.termSortSet = termSortSet;
        this.services = services;
        addMutations();
    }

    public int getGenerations() {
        return generations;
    }

    public void setGenerations(int generations) {
        this.generations = generations;
    }

    public int getPopulationSize() {
        return populationSize;
    }

    public void setPopulationSize(int populationSize) {
        this.populationSize = populationSize;
        this.replacementStrategy.setPopulationSize(populationSize);
    }

    public double getReplacementRate() {
        return replacementRate;
    }

    public void setReplacementRate(double replacementRate) {
        if (replacementRate >= 0 && replacementRate <= 1) {
            this.replacementRate = replacementRate;
        }
    }

    public int getEvaluationThreads() {
        return evaluationThreads;
    }

    public void setEvaluationThreads(int evaluationThreads) {
        this.evaluationThreads = evaluationThreads;
        evaluationStrategy.setThreadPoolSize(evaluationThreads);
    }

    public AbstractEvaluationStrategy getEvaluationStrategy() {
        return evaluationStrategy;
    }

    public AbstractReplacementStrategy getReplacementStrategy() {
        return replacementStrategy;
    }

    public List<Mutation> getMutations() {
        return mutations;
    }

    public List<Integer> getMutationProbabilities() {
        return mutationProbabilities;
    }

    public Map<Sort, RandomAccessSet<Term>> getTermSortSet() {
        return termSortSet;
    }

    private void addMutations() {
        mutations.add(new AddConjunctMutation(services, termPool));
        mutationProbabilities.add(2);

        mutations.add(new AddDisjunctMutation(services, termPool));
        mutationProbabilities.add(mutationProbabilities.getLast() + 2);

        mutations.add(new DeleteConjunctMutation());
        mutationProbabilities.add(mutationProbabilities.getLast() + 2);

        mutations.add(new DeleteDisjunctMutation());
        mutationProbabilities.add(mutationProbabilities.getLast() + 2);

        mutations.add(new NegateConjunctMutation());
        mutationProbabilities.add(mutationProbabilities.getLast() + 1);

        mutations.add(new NegateDisjunctMutation());
        mutationProbabilities.add(mutationProbabilities.getLast() + 1);

        mutations.add(new StrengthenWeakenMutation(services));
        mutationProbabilities.add(mutationProbabilities.getLast() + 2);

        mutations.add(new ReplaceVariableMutation(termSortSet));
        mutationProbabilities.add(mutationProbabilities.getLast() + 12);
    }

    public void setTermPool(Term[] termPool) {
        this.termPool = termPool;
    }
}
