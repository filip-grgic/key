package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.mutations;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.Map;

public class ReplaceVariableMutation extends Mutation {
    public ReplaceVariableMutation(Map<Sort, RandomAccessSet<Term>> termSortSet) {
        super(null, null, termSortSet);
    }

    @Override
    public void mutate(LoopInvariantFreeGenome genome) {
        Term genomeTerm = genome.getContainingTerms().getRandomElement();
        RandomAccessSet<Term> sortedPool = termSortSet.get(genomeTerm.sort());

        Term globalTerm = genomeTerm;

        while (globalTerm.equals(genomeTerm)) {
            globalTerm = sortedPool.getRandomElement();
        }

        genome.replaceTerm(genomeTerm, globalTerm);

//        Map<Name, Sort> genomeVariableNameMap = genome.getProgramVariableNameMap();
//        int genomeSetIndex = random.nextInt(genomeVariableNameMap.size());
//
//        Name genomeLocVariableName = null;
//        Sort genomeLocVariableSort = null;
//        LocationVariable globalLocVariable = null;
//
//        for (Name genomePotentialVariableName : genomeVariableNameMap.keySet()) {
//            if (genomeSetIndex == 0) {
//                genomeLocVariableName = genomePotentialVariableName;
//                genomeLocVariableSort = genomeVariableNameMap.get(genomePotentialVariableName);
//                break;
//            }
//            genomeSetIndex--;
//        }
//
//        Sort finalGenomeLocVariableSort = genomeLocVariableSort;
//        List<LocationVariable> sortedVars = programVariableSet.stream()
//                .filter((variable) -> variable.sort() == finalGenomeLocVariableSort).toList();
//        int sortedVarsIndex = random.nextInt(sortedVars.size());
//        globalLocVariable = sortedVars.get(sortedVarsIndex);
//
//        genome.replaceVariable(genomeLocVariableName, genomeLocVariableSort, globalLocVariable);
    }

    @Override
    public boolean suitableForMutation(LoopInvariantFreeGenome genome) {
        return genome.size() > 0;
    }
}
