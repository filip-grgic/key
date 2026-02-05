package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.evaluation;

import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures.LoopInvariantFreeGenome;

import java.util.List;

public interface IEvaluationStrategy {

    void evaluate(List<LoopInvariantFreeGenome> genomeList);

    boolean hasSolution();

    LoopInvariantFreeGenome getSolution();

}
