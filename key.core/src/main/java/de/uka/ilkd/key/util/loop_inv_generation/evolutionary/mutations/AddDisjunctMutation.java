package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;

import java.util.Random;

public class AddDisjunctMutation extends Mutation {
    private final Term[] termPool;

    public AddDisjunctMutation(EvolutionEngineParameters parameters) {
        super(parameters);
        this.termPool = parameters.getTermPool();
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        Term term = termPool[random.nextInt(termPool.length)];
        genome.getRandomPostcondition().add(new LoopInvariantFreeGen(services, term));
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0 && termPool != null && termPool.length > 0;
    }
}
