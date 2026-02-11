package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.*;

public abstract class Mutation {

    protected final EvolutionEngineParameters parameters;
    protected final Services services;

    protected Mutation(EvolutionEngineParameters parameters) {
        this.parameters = parameters;
        this.services = parameters.getServices();
    }

    public abstract void mutate(LoopInvariantFreeGenome genome);

    public abstract boolean suitableForMutation(LoopInvariantFreeGenome genome);

    public static void mutateChild(LoopInvariantFreeGenome child, EvolutionEngineParameters parameters) {
        Random random = new Random();
        List<Mutation> mutations = parameters.getMutations();
        List<Integer> probabilities = parameters.getMutationProbabilities();

        List<Mutation> possibleMutations = new ArrayList<>(mutations);
        List<Integer> possibleMutationsProbabilities = new ArrayList<>(probabilities);
        Mutation mutation = null;

        if (parameters.getReplaceReturnValueMutation().suitableForMutation(child)) {
            mutation = parameters.getReplaceReturnValueMutation();
        }

        while (!possibleMutations.isEmpty() && mutation != null) {
            int index = Collections.binarySearch(possibleMutationsProbabilities, random.nextInt(possibleMutationsProbabilities.getLast()));
            if (index < 0) {
                index = -index - 1;
            }

            Mutation potentialMutation = mutations.get(index);
            if (potentialMutation.suitableForMutation(child)) {
                mutation = potentialMutation;
                break;
            } else {
                possibleMutations.remove(index);
                int probUpdate = (index > 0) ? possibleMutationsProbabilities.get(index-1) : 0;
                probUpdate = possibleMutationsProbabilities.get(index) - probUpdate;
                List<Integer> probsPrefix = new ArrayList<>(possibleMutationsProbabilities.subList(0, index));
                for (int i = index + 1; i < possibleMutationsProbabilities.size(); i++) {
                    probsPrefix.add(possibleMutationsProbabilities.get(i) - probUpdate);
                }
                possibleMutationsProbabilities = probsPrefix;
            }
        }

        if (mutation != null) {
            mutation.mutate(child);
        }
    }

}
