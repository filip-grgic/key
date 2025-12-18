package de.uka.ilkd.key.util.loop_inv_generation.structures;

import de.uka.ilkd.key.java.Services;

import java.util.ArrayList;
import java.util.List;

public class LoopInvariantGenome {

    private List<List<LoopInvariantFreeGen>> conjuncts;
    private final Services services;

    public LoopInvariantGenome(Services services) {
        this.conjuncts = new ArrayList<>();
        this.services = services;
    }

    public void addConjunct(List<LoopInvariantFreeGen> conjunct) {
        this.conjuncts.add(conjunct);
    }

    public void removeConjunct(int index) {
        if (index >= 0 && index < conjuncts.size()) {
            conjuncts.remove(index);
        }
    }

    public void addDisjunct(LoopInvariantFreeGen disjunct, int index) {
        if (index >= 0 && index < conjuncts.size()) {
            List<LoopInvariantFreeGen> conjunct = conjuncts.get(index);
            conjunct.add(disjunct);
        }
    }

    public void removeDisjunct(int conjunctIndex, int disjunctIndex) {
        if (conjunctIndex >= 0 && conjunctIndex < conjuncts.size() &&
                disjunctIndex >= 0 && disjunctIndex < conjuncts.get(conjunctIndex).size()) {
            conjuncts.get(conjunctIndex).remove(disjunctIndex);
        }
    }


}
