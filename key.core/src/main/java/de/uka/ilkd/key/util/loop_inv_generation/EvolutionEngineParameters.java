package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.mutations.*;
import org.key_project.logic.Term;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class EvolutionEngineParameters {

    //Negative amount of generations signals infinite amounts
    private int generations = -1;
    private int populationSize = 10;
    private double replacementRate = 0.5;
    private final List<Mutation> mutations = new ArrayList<>();
    private Term[] termPool;
    private final Set<LocationVariable> programVariableSet;
    private final Services services;

    public EvolutionEngineParameters(Set<LocationVariable> programVariableSet, Services services) {
        this.programVariableSet = programVariableSet;
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
    }

    public double getReplacementRate() {
        return replacementRate;
    }

    public void setReplacementRate(double replacementRate) {
        if (replacementRate >= 0 && replacementRate <= 1) {
            this.replacementRate = replacementRate;
        }
    }

    public List<Mutation> getMutations() {
        return mutations;
    }

    private void addMutations() {
        mutations.add(new AddConjunctMutation(services, termPool));
        mutations.add(new AddDisjunctMutation(services, termPool));
        mutations.add(new DeleteConjunctMutation());
        mutations.add(new DeleteDisjunctMutation());
        mutations.add(new NegateConjunctMutation());
        mutations.add(new NegateDisjunctMutation());
        mutations.add(new ReplaceVariableMutation(programVariableSet));
    }

    public void setTermPool(Term[] termPool) {
        this.termPool = termPool;
    }
}
