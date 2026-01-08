package de.uka.ilkd.key.util.loop_inv_generation.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;


public class AddConjunctMutation extends Mutation {

    public AddConjunctMutation(Services services, Term[] termPool) {
        super(services, termPool, null);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        Term term = termPool[random.nextInt(termPool.length)];
        genome.addConjunct(new LoopInvariantFreeGen(services, term));
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return termPool != null && termPool.length > 0;
    }
}
