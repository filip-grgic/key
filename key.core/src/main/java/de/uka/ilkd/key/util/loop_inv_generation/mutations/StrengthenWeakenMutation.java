package de.uka.ilkd.key.util.loop_inv_generation.mutations;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.Map;

public class StrengthenWeakenMutation extends Mutation{
    public StrengthenWeakenMutation(Services services) {
        super(services, null, null);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        TermBuilder termBuilder = services.getTermBuilder();
        RandomAccessSet<LoopInvariantFreeGen> conjunct = genome.getRandomConjunct();
        LoopInvariantFreeGen disjunct = conjunct.getRandomElement();
        Term disjunctTerm = disjunct.getTerm();
        Term newTerm;

        if (disjunctTerm.op().name().toString().equals("lt")) {
            newTerm = termBuilder.leq((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
        } else if (disjunctTerm.op().name().toString().equals("leq")) {
            newTerm = termBuilder.lt((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
        } else {
            return;
        }

        LoopInvariantFreeGen newDisjunct = new LoopInvariantFreeGen(services, newTerm);
        if (disjunct.isNegated()) {
            newDisjunct.negate();
        }

        conjunct.remove(disjunct);
        conjunct.add(newDisjunct);
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0;
    }
}
