package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;

import java.util.List;
import java.util.Random;

public class DeleteDisjunctMutation extends Mutation {
    public DeleteDisjunctMutation(EvolutionEngineParameters parameters) {
        super(parameters);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        List<LoopInvariantFreeGen> postcondition = genome.getRandomPostcondition();
        if (postcondition.size() > 1) {
            int index = random.nextInt(postcondition.size());
            postcondition.remove(index);
        } else {
            genome.getPostconditions().remove(postcondition);
        }
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 1 || (genome.size() == 1 && genome.getRandomPostcondition().size() > 1);
    }
}
