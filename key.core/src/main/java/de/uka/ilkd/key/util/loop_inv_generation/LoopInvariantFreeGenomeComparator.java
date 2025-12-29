package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;

import java.util.Comparator;

public class LoopInvariantFreeGenomeComparator implements Comparator<LoopInvariantFreeGenome> {
    @Override
    public int compare(LoopInvariantFreeGenome o1, LoopInvariantFreeGenome o2) {
        return Double.compare(o1.getFitness(), o2.getFitness());
    }
}
