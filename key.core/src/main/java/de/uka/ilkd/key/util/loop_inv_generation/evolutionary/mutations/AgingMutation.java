package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;

import java.util.Random;

public class AgingMutation extends Mutation {
    public AgingMutation(EvolutionEngineParameters parameters) {
        super(parameters);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        TermBuilder termBuilder = services.getTermBuilder();
        Term one = services.getTermBuilder().one();

        Term term = genome.getContainingTerms().getRandomElement();
        Term mutatedTerm;

        if (random.nextBoolean()) {
            if (term.op().name().toString().equals("sub") && term.sub(1).equals(one)) {
                mutatedTerm = term.sub(0);
            } else {
                mutatedTerm = termBuilder.add((JTerm) term, (JTerm) one);
            }
        } else {
            if (term.op().name().toString().equals("add") && term.sub(1).equals(one)) {
                mutatedTerm = term.sub(0);
            } else {
                mutatedTerm = termBuilder.func(services.getTypeConverter().getIntegerLDT().getSub(), (JTerm) term, (JTerm) one);
            }
        }

        genome.replaceTerm(term, mutatedTerm);
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return !genome.getContainingTerms().isEmpty();
    }
}
