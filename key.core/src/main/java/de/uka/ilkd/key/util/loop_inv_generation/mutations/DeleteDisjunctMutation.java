package de.uka.ilkd.key.util.loop_inv_generation.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;

import java.util.Random;

public class DeleteDisjunctMutation extends Mutation {
    public DeleteDisjunctMutation() {
        super(null, null, null);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        int conjunctIndex = random.nextInt(genome.size());
        int disjunctIndex = random.nextInt(genome.getConjunctSize(conjunctIndex));
        genome.removeDisjunct(conjunctIndex, disjunctIndex);
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 1 || (genome.size() == 1 && genome.getConjunctSize(0) > 1);
    }
}
