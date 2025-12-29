package de.uka.ilkd.key.util.loop_inv_generation.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;

public abstract class Mutation {

    protected Term[] termPool;
    protected Services services;

    protected Mutation(Services services, Term[] termPool) {
        this.termPool = termPool;
        this.services = services;
    }

    public abstract void mutate(LoopInvariantFreeGenome genome);

    public abstract boolean suitableForMutation(LoopInvariantFreeGenome genome);

}
