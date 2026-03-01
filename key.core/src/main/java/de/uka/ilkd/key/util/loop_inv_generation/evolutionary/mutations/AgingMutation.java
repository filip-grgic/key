package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.smt.model.Location;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantLimitingGen;
import org.key_project.logic.Term;

import java.util.Random;
import java.util.Set;

public class AgingMutation extends Mutation {
    public AgingMutation(EvolutionEngineParameters parameters) {
        super(parameters);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        TermBuilder tb = services.getTermBuilder();

        Set<LocationVariable> keySet = genome.getLimitingGenes().keySet();
        int index = random.nextInt(keySet.size());

        LoopInvariantLimitingGen limitingGen = null;

        for (LocationVariable key : keySet) {
            if (index == 0) {
                limitingGen = genome.getLimitingGenes().get(key);
                break;
            }
            index--;
        }

        assert limitingGen != null;

        Term limit;

        if (random.nextBoolean() && limitingGen.getLowerLimit() != null) {
            limit = limitingGen.getLowerLimit();
        } else {
            limit = limitingGen.getUpperLimit();
        }

        if (limit == null) {
            return;
        }

        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        if (random.nextBoolean()) {
            if (limit.op().equals(integerLDT.getSub()) && limit.sub(1).equals(tb.one())) {
                limitingGen.replaceTerm(limit, limit.sub(0));
            } else {
                limitingGen.replaceTerm(limit, tb.add((JTerm) limit, tb.one()));
            }
        } else {
            if (limit.op().equals(integerLDT.getAdd()) && limit.sub(1).equals(tb.one())) {
                limitingGen.replaceTerm(limit, limit.sub(0));
            } else {
                limitingGen.replaceTerm(limit, tb.func(integerLDT.getSub(), (JTerm) limit, tb.one()));
            }
        }
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return !genome.getLimitingGenes().isEmpty();
    }
}
