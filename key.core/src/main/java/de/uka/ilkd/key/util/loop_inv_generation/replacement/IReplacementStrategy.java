package de.uka.ilkd.key.util.loop_inv_generation.replacement;

import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;

import java.util.List;

public interface IReplacementStrategy {

    List<LoopInvariantFreeGenome> replace(List<LoopInvariantFreeGenome> population,
                                          List<LoopInvariantFreeGenome> mutatedChildren);

}
