package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;

public class DeleteDisjunctMutation extends Mutation {
    public DeleteDisjunctMutation() {
        super(null, null, null);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        RandomAccessSet<LoopInvariantFreeGen> conjunct = genome.getRandomConjunct();
        if (conjunct.size() > 1) {
            conjunct.removeRandomElement();
        } else {
            genome.getConjuncts().remove(conjunct);
        }
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 1 || (genome.size() == 1 && genome.getRandomConjunct().size() > 1);
    }
}
