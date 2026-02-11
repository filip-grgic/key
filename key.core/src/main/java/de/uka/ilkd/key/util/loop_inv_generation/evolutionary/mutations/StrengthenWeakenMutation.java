package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;

import java.util.Random;

public class StrengthenWeakenMutation extends Mutation {
    public StrengthenWeakenMutation(EvolutionEngineParameters parameters) {
        super(parameters);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        TermBuilder termBuilder = services.getTermBuilder();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        RandomAccessSet<LoopInvariantFreeGen> conjunct = genome.getRandomConjunct();
        LoopInvariantFreeGen disjunct = conjunct.getRandomElement();
        Term disjunctTerm = disjunct.getTerm();
        Term newTerm;

        if (disjunctTerm.op().equals(integerLDT.getLessThan())) {
            newTerm = termBuilder.leq((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
        }

        else if (disjunctTerm.op().equals(integerLDT.getGreaterThan())) {
            newTerm = termBuilder.geq((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
        }

        else if (disjunctTerm.op().equals(Equality.EQUALS)) {
            if (random.nextBoolean()) {
                newTerm = termBuilder.geq((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
            } else {
                newTerm = termBuilder.leq((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
            }
        }

        else if (disjunctTerm.op().equals(integerLDT.getGreaterOrEquals())) {
            if (random.nextBoolean()) {
                newTerm = termBuilder.gt((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
            } else {
                newTerm = termBuilder.equals((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
            }
        }

        else if (disjunctTerm.op().equals(integerLDT.getLessOrEquals())) {
            if (random.nextBoolean()) {
                newTerm = termBuilder.lt((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
            } else {
                newTerm = termBuilder.equals((JTerm) disjunct.getLeft(), (JTerm) disjunct.getRight());
            }
        }

        else {
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
