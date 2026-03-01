package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations.Mutation;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantLimitingGen;
import org.key_project.logic.Term;

import java.util.Random;

public class GenomeGenerator {

    public static LoopInvariantFreeGenome generateGenome(EvolutionEngineParameters parameters) {
        Random random = new Random();

        LoopInvariantFreeGenome genome = new LoopInvariantFreeGenome(parameters.getServices(),
                parameters.getVerificationConditions(), parameters.getPostconditions());

        for (LocationVariable changingVariable : parameters.getChangingVariables()) {
            LoopInvariantLimitingGen gen = generateLimitingGen(parameters, changingVariable);

            if (gen != null) {
                genome.addLimitingGen(gen);
            }
        }

        if (parameters.getReplaceReturnValueMutation().suitableForMutation(genome)) {
            parameters.getReplaceReturnValueMutation().mutate(genome);
        }

        int mutationAmount = random.nextInt(4);

        for (int i = 0; i < mutationAmount; i++) {
            Mutation.mutateChild(genome, parameters);
        }

        return genome;
    }

    private static LoopInvariantLimitingGen generateLimitingGen(EvolutionEngineParameters parameters, LocationVariable variable) {
        Random random = new Random();
        TermBuilder tb = parameters.getServices().getTermBuilder();
        if (random.nextBoolean()) {

            Term lowerLimit = null;
            Term upperLimit = null;

            if (random.nextBoolean()) {
                lowerLimit = tb.var(parameters.getAllVariables().getRandomElement());
            }

            if (random.nextBoolean()) {
                upperLimit = tb.var(parameters.getAllVariables().getRandomElement());
            }

            if (lowerLimit != null || upperLimit != null) {
                return new LoopInvariantLimitingGen(parameters.getServices(), variable, lowerLimit, upperLimit);
            }

        }

        return null;
    }

}
