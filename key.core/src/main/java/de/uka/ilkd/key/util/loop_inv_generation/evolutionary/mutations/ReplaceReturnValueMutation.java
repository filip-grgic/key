package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.Map;

public class ReplaceReturnValueMutation extends ReplaceVariableMutation {
    public ReplaceReturnValueMutation(Map<Sort, RandomAccessSet<Term>> termSortSet) {
        super(termSortSet);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Term genomeTerm = genome.getReturnValue();
        RandomAccessSet<Term> sortedPool = termSortSet.get(genomeTerm.sort());

        Term globalTerm = genomeTerm;

        while (globalTerm.equals(genomeTerm)) {
            globalTerm = sortedPool.getRandomElement();
        }

        genome.replaceTerm(genomeTerm, globalTerm);
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0 && genome.containsReturnValue();
    }
}
