package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;

public class NegateDisjunctMutation extends Mutation {
    public NegateDisjunctMutation(EvolutionEngineParameters parameters) {
        super(parameters);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        //TODO: Check later whether impactfulness
        //genome.getRandomPostcondition().getRandomElement().negate();
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0;
    }
}
