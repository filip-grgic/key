package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.Map;

public abstract class Mutation {

    protected Term[] termPool;
    protected Services services;
    protected final Map<Sort, RandomAccessSet<Term>> termSortSet;

    protected Mutation(Services services, Term[] termPool, Map<Sort, RandomAccessSet<Term>> termSortSet) {
        this.termPool = termPool;
        this.services = services;
        this.termSortSet = termSortSet;
    }

    public abstract void mutate(LoopInvariantFreeGenome genome);

    public abstract boolean suitableForMutation(LoopInvariantFreeGenome genome);

}
