package de.uka.ilkd.key.util.loop_inv_generation.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.LoopInvariantFreeGenomeComparator;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class LoopInvariantFreeGenome {

    private static LoopInvariantFreeGenomeComparator comparator;

    private List<List<LoopInvariantFreeGen>> conjuncts;
    private final Services services;
    private double fitness;
    private boolean changedSinceCalc;
    private boolean isSolution;

    public static LoopInvariantFreeGenomeComparator getComparator() {
        if (comparator == null) {
            comparator = new LoopInvariantFreeGenomeComparator();
        }
        return comparator;
    }

    public LoopInvariantFreeGenome(Services services) {
        this.conjuncts = new ArrayList<>();
        this.services = services;
    }

    public void checkFitness() {
        //TODO: Calculate fitness as amount of satisfied verificationConditions + 1 (+1 necessary s.t. the overall fitness can't be 0)
        //TODO: Check whether it is a solution
        changedSinceCalc = false;
    }

    public LoopInvariantFreeGenome combine(LoopInvariantFreeGenome other) {
        Random random = new Random();
        LoopInvariantFreeGenome result = new LoopInvariantFreeGenome(services);

        for (List<LoopInvariantFreeGen> conjunct : conjuncts) {
            if (random.nextDouble() < 0.5) {
                result.conjuncts.add(conjunct);
            }
        }

        for (List<LoopInvariantFreeGen> conjunct : other.conjuncts) {
            if (random.nextDouble() < 0.5) {
                result.conjuncts.add(conjunct);
            }
        }

        return result;
    }

    public double getFitness() {
        return fitness;
    }

    public boolean isSolution() {
        return isSolution;
    }

    /**
     * Returns the amount of conjuncts in the genome.
     * @return the amount of conjuncts in the genome
     */
    public int size() {
        return conjuncts.size();
    }

    /**
     * Return the amount of disjuncts in the conjunct at the specified index.
     * @param index of the conjunct in the genome
     * @return the amount of disjuncts in the conjunct at the specified index
     */
    public int getConjunctSize(int index) {
        if (index >= 0 && index < conjuncts.size()) {
            return conjuncts.get(index).size();
        }

        return 0;
    }

    public void addConjunct(List<LoopInvariantFreeGen> conjunct) {
        this.conjuncts.add(conjunct);
        changedSinceCalc = true;
    }

    public void addConjunct(LoopInvariantFreeGen conjunct) {
        List<LoopInvariantFreeGen> newConjunct = new ArrayList<>();
        newConjunct.add(conjunct);
        addConjunct(newConjunct);
    }

    public void removeConjunct(int index) {
        if (index >= 0 && index < conjuncts.size()) {
            conjuncts.remove(index);
        }
        changedSinceCalc = true;

    }

    public void negateConjunct(int index) {
        if (index >= 0 && index < conjuncts.size()) {
            List<LoopInvariantFreeGen> conjunct = conjuncts.remove(index);
            for (LoopInvariantFreeGen disjunct: conjunct) {
                disjunct.negate();
                addConjunct(disjunct);
            }
            changedSinceCalc = true;
        }
    }

    public void addDisjunct(LoopInvariantFreeGen disjunct, int index) {
        if (index >= 0 && index < conjuncts.size()) {
            List<LoopInvariantFreeGen> conjunct = conjuncts.get(index);
            conjunct.add(disjunct);
            changedSinceCalc = true;
        }

    }

    public void removeDisjunct(int conjunctIndex, int disjunctIndex) {
        if (conjunctIndex >= 0 && conjunctIndex < conjuncts.size() &&
                disjunctIndex >= 0 && disjunctIndex < conjuncts.get(conjunctIndex).size()) {

            if (getConjunctSize(conjunctIndex) == 1) {
                removeConjunct(conjunctIndex);
            } else {
                conjuncts.get(conjunctIndex).remove(disjunctIndex);
            }
            changedSinceCalc = true;
        }
    }

    public void negateDisjunct(int conjunctIndex, int disjunctIndex) {
        if (conjunctIndex >= 0 && conjunctIndex < conjuncts.size() &&
                disjunctIndex >= 0 && disjunctIndex < conjuncts.get(conjunctIndex).size()) {
            conjuncts.get(conjunctIndex).get(disjunctIndex).negate();
            changedSinceCalc = true;
        }
    }

    public boolean containsProgramVariable(LocationVariable programVariable) {
        if (programVariable == null) {
            return false;
        }
        for (List<LoopInvariantFreeGen> conjunct : conjuncts) {
            for (LoopInvariantFreeGen disjunct : conjunct) {
                if (disjunct.containsProgramVariable(programVariable)) {
                    return true;
                }
            }
        }

        return false;
    }
}
