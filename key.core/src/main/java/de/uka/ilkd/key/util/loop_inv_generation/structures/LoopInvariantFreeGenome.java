package de.uka.ilkd.key.util.loop_inv_generation.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JAbstractSortedOperator;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.LoopInvariantFreeGenomeComparator;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.prover.sequent.Sequent;

import java.util.*;

public class LoopInvariantFreeGenome {

    private static LoopInvariantFreeGenomeComparator comparator;

    private final List<List<LoopInvariantFreeGen>> conjuncts;
    private final Services services;
    private double fitness;
    private boolean changedSinceCalc;
    private boolean isSolution;
    private Set<Name> programVariableNameSet;
    private boolean nameSetRefreshed;
    private final VerificationCondition[] verificationConditions;

    public static LoopInvariantFreeGenomeComparator getComparator() {
        if (comparator == null) {
            comparator = new LoopInvariantFreeGenomeComparator();
        }
        return comparator;
    }

    public LoopInvariantFreeGenome(Services services, VerificationCondition[] verificationConditions) {
        this.conjuncts = new ArrayList<>();
        this.services = services;
        this.verificationConditions = verificationConditions;
        programVariableNameSet =  new HashSet<>();
        nameSetRefreshed = true;
    }

    public LoopInvariantFreeGenome(Services services) {
        this(services, new VerificationCondition[0]);
    }

    public void checkFitness() {
        //TODO: Try different Fitness strategies: e.g. weighted VCs depending on how many generations they have been fulfilled
        fitness = 0;
        isSolution = true;
        for (VerificationCondition vc : verificationConditions) {
            if (vc.checkFulfillment(this)) {
                fitness += 1;
            } else {
                isSolution = false;
            }
        }

        fitness += 1;

        changedSinceCalc = false;
    }

    public Term translateToTerm() {
        TermBuilder termBuilder = services.getTermBuilder();

        Term conjunction = null;
        for (List<LoopInvariantFreeGen> conjunct : conjuncts) {
            Term disjunction = null;
            for (LoopInvariantFreeGen disjunct : conjunct) {
                if (disjunction == null) {
                    disjunction = disjunct.translateToTerm();
                } else {
                    disjunction = termBuilder.or((JTerm) disjunction, (JTerm) disjunct.translateToTerm());
                }
            }

            if (conjunction == null) {
                conjunction = disjunction;
            } else {
                conjunction = termBuilder.and((JTerm) conjunction, (JTerm) disjunction);
            }
        }

        return conjunction;
    }

    /**
     * Create a new genome for the recombination phase by randomly selecting conjuncts of both genomes and create
     * a new conjunction that is used for the child. The child with the resulting conjunction is then returned.
     * @param other the other parent genome used for the recombination
     * @return a recombination of the conjuncts of this and other
     */
    public LoopInvariantFreeGenome combine(LoopInvariantFreeGenome other) {
        Random random = new Random();
        LoopInvariantFreeGenome result = new LoopInvariantFreeGenome(services, verificationConditions);

        if (other == null || (this.conjuncts.isEmpty() && other.conjuncts.isEmpty())) {
            return result;
        }

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

        if (result.size() == 0) {
            LoopInvariantFreeGenome chosen;
            if (!this.conjuncts.isEmpty() && random.nextDouble() < 0.5) {
                chosen = this;
            } else {
                chosen = other;
            }

            int conjunctIndex = random.nextInt(chosen.size());
            result.conjuncts.add(chosen.conjuncts.get(conjunctIndex));
        }

        return result;
    }

    public double getFitness() {
        if (changedSinceCalc) {
            checkFitness();
        }
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

    public List<List<LoopInvariantFreeGen>> getConjuncts() {
        return conjuncts;
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
        List<LoopInvariantFreeGen> newConjunct = new ArrayList<>();
        for (LoopInvariantFreeGen disjunct: conjunct) {
            newConjunct.add(new LoopInvariantFreeGen(disjunct));
            programVariableNameSet.addAll(disjunct.getProgramVariableNameSet());
        }
        this.conjuncts.add(newConjunct);
        changedSinceCalc = true;
        nameSetRefreshed = false;
    }

    public void addConjunct(LoopInvariantFreeGen conjunct) {
        List<LoopInvariantFreeGen> newConjunct = new ArrayList<>();
        newConjunct.add(conjunct);
        addConjunct(newConjunct);
    }

    public void removeConjunct(int index) {
        if (index >= 0 && index < conjuncts.size()) {
            conjuncts.remove(index);
            changedSinceCalc = true;
            nameSetRefreshed = false;
        }

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
            conjunct.add(new LoopInvariantFreeGen(disjunct));
            changedSinceCalc = true;
            nameSetRefreshed = false;
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
            nameSetRefreshed = false;
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
        refreshProgramVariableNameSet();

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

    public void replaceVariable(Name oldVariable, JAbstractSortedOperator newVariable) {
        for (List<LoopInvariantFreeGen> conjunct: conjuncts) {
            for (LoopInvariantFreeGen disjunct: conjunct) {
                disjunct.replaceVariable(oldVariable, newVariable);
            }
        }

        nameSetRefreshed = false;
    }

    public Set<Name> getProgramVariableNameSet() {
        refreshProgramVariableNameSet();
        return programVariableNameSet;
    }

    private void refreshProgramVariableNameSet() {
        if (nameSetRefreshed) {
            return;
        }

        programVariableNameSet = new HashSet<>();
        for (List<LoopInvariantFreeGen> conjunct : conjuncts) {
            for (LoopInvariantFreeGen disjunct : conjunct) {
                programVariableNameSet.addAll(disjunct.getProgramVariableNameSet());
            }
        }
        nameSetRefreshed = true;
    }

    public LoopInvariantFreeGenome copy() {
        LoopInvariantFreeGenome newGenome = new LoopInvariantFreeGenome(services, verificationConditions);
        for (List<LoopInvariantFreeGen> conjunct: conjuncts) {
            List<LoopInvariantFreeGen> newConjunct = new ArrayList<>();
            for (LoopInvariantFreeGen disjunct: conjunct) {
                newConjunct.add(disjunct.copy());
            }
            newGenome.addConjunct(newConjunct);
        }

        return newGenome;
    }

}
