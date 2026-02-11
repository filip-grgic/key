package de.uka.ilkd.key.util.loop_inv_generation.evolutionary;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation.AbstractEvaluationStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation.EvaluationStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations.*;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.replacement.AbstractReplacementStrategy;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.replacement.MixingWithImmigrationReplacement;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.VerificationCondition;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.*;

public class EvolutionEngineParameters {

    private final VerificationCondition[] verificationConditions;
    //Negative amount of generations signals infinite amounts
    private int generations = -1;
    private int populationSize = 10;
    private double replacementRate = 1;
    private int evaluationThreads = 4;
    private final List<Mutation> mutations = new ArrayList<>();
    private final List<Integer> mutationProbabilities = new ArrayList<>();
    private ReplaceReturnValueMutation replaceReturnValueMutation;
    private final AbstractEvaluationStrategy evaluationStrategy;
//    private final AbstractReplacementStrategy replacementStrategy = new GenerationalMixingReplacement(populationSize, evaluationStrategy);
    private final AbstractReplacementStrategy replacementStrategy;
    private Term[] termPool;
    private RandomAccessSet<LocationVariable> allVariables;
    private RandomAccessSet<LocationVariable> changingVariables;
    protected final Map<Sort, RandomAccessSet<Term>> termSortSet;
    private final Services services;

    public EvolutionEngineParameters(Term[] termPool,
                                     RandomAccessSet<LocationVariable> allVariables,
                                     RandomAccessSet<LocationVariable> changingVariables,
                                     Map<Sort, RandomAccessSet<Term>> termSortSet,
                                     Services services,
                                     VerificationCondition[] verificationConditions) {
        this.termPool = termPool;
        this.allVariables = allVariables;
        this.changingVariables = changingVariables;
        this.termSortSet = termSortSet;
        this.services = services;
        this.verificationConditions = verificationConditions;
        this.evaluationStrategy = new EvaluationStrategy(evaluationThreads);
        this.replacementStrategy = new MixingWithImmigrationReplacement(0.3, 0.3, this, services, evaluationStrategy);
        this.replaceReturnValueMutation = new ReplaceReturnValueMutation(this);
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

    public VerificationCondition[] getVerificationConditions() {
        return verificationConditions;
    }

    public double getReplacementRate() {
        return replacementRate;
    }

    public void setReplacementRate(double replacementRate) {
        if (replacementRate >= 0 && replacementRate <= 1) {
            this.replacementRate = replacementRate;
        }
    }

    public Term[] getTermPool() {
        return termPool;
    }

    public Services getServices() {
        return services;
    }

    public int getEvaluationThreads() {
        return evaluationThreads;
    }

    public void setEvaluationThreads(int evaluationThreads) {
        this.evaluationThreads = evaluationThreads;
        evaluationStrategy.setThreadPoolSize(evaluationThreads);
    }

    public RandomAccessSet<LocationVariable> getAllVariables() {
        return allVariables;
    }

    public RandomAccessSet<LocationVariable> getChangingVariables() {
        return changingVariables;
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
//        addMutation(new AddConjunctMutation(this), 2);
//        addMutation(new AddDisjunctMutation(this), 2);
//        addMutation(new DeleteConjunctMutation(this), 2);
//        addMutation(new DeleteDisjunctMutation(this), 2);
//        addMutation(new NegateConjunctMutation(this), 1);
//        addMutation(new NegateDisjunctMutation(this), 1);
        addMutation(new StrengthenWeakenMutation(this), 2);
        addMutation(new ReplaceVariableMutation(this), 12);
    }

    private void addMutation(Mutation mutation, int probabilityShares) {
        mutations.add(mutation);
        if (mutationProbabilities.isEmpty()) {
            mutationProbabilities.add(probabilityShares);
        } else {
            mutationProbabilities.add(mutationProbabilities.getLast() + probabilityShares);
        }
    }

    public ReplaceReturnValueMutation getReplaceReturnValueMutation() {
        return replaceReturnValueMutation;
    }

    public void setTermPool(Term[] termPool) {
        this.termPool = termPool;
    }
}
