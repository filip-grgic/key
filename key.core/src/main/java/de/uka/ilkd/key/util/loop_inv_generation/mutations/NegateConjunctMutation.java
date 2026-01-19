package de.uka.ilkd.key.util.loop_inv_generation.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;

import java.util.Random;

public class NegateConjunctMutation extends Mutation {
    public NegateConjunctMutation() {
        super(null, null, null);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        genome.negateRandomConjunct();
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0;
    }
}
