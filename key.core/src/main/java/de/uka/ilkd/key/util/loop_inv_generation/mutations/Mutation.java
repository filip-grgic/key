package de.uka.ilkd.key.util.loop_inv_generation.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;

import java.util.Set;

public abstract class Mutation {

    protected Term[] termPool;
    protected Services services;
    protected final Set<LocationVariable> programVariableSet;

    protected Mutation(Services services, Term[] termPool, Set<LocationVariable> programVariableSet) {
        this.termPool = termPool;
        this.services = services;
        this.programVariableSet = programVariableSet;
    }

    public abstract void mutate(LoopInvariantFreeGenome genome);

    public abstract boolean suitableForMutation(LoopInvariantFreeGenome genome);

}
