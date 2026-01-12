package de.uka.ilkd.key.util.loop_inv_generation.mutations;

import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import org.key_project.logic.Name;

import java.util.Random;
import java.util.Set;

public class ReplaceVariableMutation extends Mutation {
    public ReplaceVariableMutation(Set<LocationVariable> programVariableSet) {
        super(null, null, programVariableSet);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Random random = new Random();
        Set<Name> genomeVariableNameSet = genome.getProgramVariableNameSet();
        int genomeSetIndex = random.nextInt(genomeVariableNameSet.size());
        int globalSetIndex = random.nextInt(programVariableSet.size());

        Name genomeLocVariableName = null;
        LocationVariable globalLocVariable = null;

        for (Name genomePotentialVariableName: genomeVariableNameSet) {
            if (genomeSetIndex == 0) {
                genomeLocVariableName = genomePotentialVariableName;
                break;
            }
            genomeSetIndex--;
        }

        for (LocationVariable globalPotentialVariable: programVariableSet) {
            if (globalSetIndex == 0) {
                globalLocVariable = globalPotentialVariable;
                break;
            }
            globalSetIndex--;
        }

        genome.replaceVariable(genomeLocVariableName, globalLocVariable);
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0 && !genome.getProgramVariableNameSet().isEmpty();
    }
}
