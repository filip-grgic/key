package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations.Mutation;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;

import java.util.Random;

public class GenomeGenerator {

    public static LoopInvariantFreeGenome generateGenome(EvolutionEngineParameters parameters) {
        Random random = new Random();
        Term newTerm;

        if (random.nextBoolean()) {
            newTerm = generateFromPostcondition(parameters);
        } else {
            newTerm = generateRandomRelation(parameters);
        }

        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(parameters.getServices(), newTerm);
        LoopInvariantFreeGenome genome = new LoopInvariantFreeGenome(parameters.getServices(), parameters.getVerificationConditions());
        genome.addConjunct(gen);

        if (parameters.getReplaceReturnValueMutation().suitableForMutation(genome)) {
            parameters.getReplaceReturnValueMutation().mutate(genome);
        }

        int mutationAmount = random.nextInt(4);

        for (int i = 0; i < mutationAmount; i++) {
            Mutation.mutateChild(genome, parameters);
        }

        return genome;
    }

    private static Term generateRandomRelation(EvolutionEngineParameters parameters) {
        Random random = new Random();
        TermBuilder termBuilder = parameters.getServices().getTermBuilder();

        RandomAccessSet<LocationVariable> changingVariables = parameters.getChangingVariables();
        RandomAccessSet<LocationVariable> allVariables = parameters.getAllVariables();

        Term left = termBuilder.var(changingVariables.getRandomElement());
        Term right = termBuilder.var(allVariables.getRandomElement());

        IntegerLDT integerLDT = parameters.getServices().getTypeConverter().getIntegerLDT();

        Function[] functions = new Function[] {
                integerLDT.getLessThan(),
                integerLDT.getGreaterThan(),
                integerLDT.getLessOrEquals(),
                integerLDT.getGreaterOrEquals(),
        };

        int index = random.nextInt(functions.length + 1);

        if (index == functions.length) {
            return termBuilder.equals((JTerm) left, (JTerm) right);
        } else {
            return termBuilder.func(functions[index], (JTerm) left, (JTerm) right);
        }
    }

    private static Term generateFromPostcondition(EvolutionEngineParameters parameters) {
        Random random = new Random();
        Term[] termPool = parameters.getTermPool();

        int index = random.nextInt(termPool.length);
        return termPool[index];
    }

}
