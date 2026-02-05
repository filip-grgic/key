package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;

import java.util.Random;

public class AddDisjunctMutation extends Mutation {
    public AddDisjunctMutation(Services services, Term[] termPool) {
        super(services, termPool, null);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        Term term = termPool[random.nextInt(termPool.length)];
        genome.getRandomConjunct().add(new LoopInvariantFreeGen(services, term));
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0 && termPool != null && termPool.length > 0;
    }
}
