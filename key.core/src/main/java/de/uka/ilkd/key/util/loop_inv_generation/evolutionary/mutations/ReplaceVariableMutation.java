package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.Map;

public class ReplaceVariableMutation extends Mutation {
    protected final Map<Sort, RandomAccessSet<Term>> termSortSet;
    private final TermBuilder termBuilder;

    public ReplaceVariableMutation(EvolutionEngineParameters parameters) {
        super(parameters);
        this.termSortSet = parameters.getTermSortSet();
        this.termBuilder = services.getTermBuilder();
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Term genomeTerm = genome.getContainingTerms().getRandomElement();
        RandomAccessSet<LocationVariable> sortedPool = parameters.getChangingVariables();

        Term globalTerm = genomeTerm;

        while (globalTerm.equals(genomeTerm)) {
            globalTerm = termBuilder.var(sortedPool.getRandomElement());
        }

        genome.replaceTerm(genomeTerm, globalTerm);
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0;
    }
}
