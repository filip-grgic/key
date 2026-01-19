package de.uka.ilkd.key.util.loop_inv_generation.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.util.loop_inv_generation.LoopInvariantFreeGenomeComparator;
import de.uka.ilkd.key.util.loop_inv_generation.util.RandomAccessSet;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.*;

public class LoopInvariantFreeGenome {

    private static LoopInvariantFreeGenomeComparator comparator;

    private final RandomAccessSet<RandomAccessSet<LoopInvariantFreeGen>> conjuncts;
    private final Services services;
    private double fitness;
    private boolean changedSinceCalc;
    private boolean isSolution;
    //    private Map<Name, Sort> programVariableNameMap;
    private RandomAccessSet<Term> containingTerms;
    private boolean containingTermsRefreshed;
    private final VerificationCondition[] verificationConditions;

    public static LoopInvariantFreeGenomeComparator getComparator() {
        if (comparator == null) {
            comparator = new LoopInvariantFreeGenomeComparator();
        }
        return comparator;
    }

    public LoopInvariantFreeGenome(Services services, VerificationCondition[] verificationConditions) {
        this.conjuncts = new RandomAccessSet<>();
        this.services = services;
        this.verificationConditions = verificationConditions;
//        programVariableNameMap =  new HashMap<>();
        containingTermsRefreshed = true;
        changedSinceCalc = true;
    }

    public LoopInvariantFreeGenome(Services services) {
        this(services, new VerificationCondition[0]);
    }

    /**
     * Calculates the current fitness of the genome by checking all provided verification conditions whether they are
     * valid or not where the genome represents the invariant candidate. The fitness score is the amount of valid
     * verification conditions + 1. The additional + 1 is necessary, as the fitness score might be used as a divisor
     * later on.
     */
    public void checkFitness() {
        if (!changedSinceCalc) {
            return;
        }

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

    /**
     * Translates the current state of the genome into a Term workable by KeY. The higher layer of {@code conjuncts} is
     * translated into a conjunction and the lower layer is translated into disjunctions. The disjuncts are translated
     * from the contained genes.
     *
     * @return The logical representation of this genome in the form of a conjunction.
     */
    public Term translateToTerm() {
        TermBuilder termBuilder = services.getTermBuilder();

        Term conjunction = null;
        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
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
     *
     * @param other the other parent genome used for the recombination
     * @return a recombination of the conjuncts of this and other
     */
    public LoopInvariantFreeGenome combine(LoopInvariantFreeGenome other) {
        LoopInvariantFreeGenome result = new LoopInvariantFreeGenome(services, verificationConditions);

        if (other == null || (this.conjuncts.isEmpty() && other.conjuncts.isEmpty())) {
            return result;
        }

        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts.union(other.conjuncts)) {
            result.addConjunct(conjunct);
        }

        result.changedSinceCalc = true;
        result.containingTermsRefreshed = false;
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
     *
     * @return the amount of conjuncts in the genome
     */
    public int size() {
        return conjuncts.size();
    }

    public RandomAccessSet<RandomAccessSet<LoopInvariantFreeGen>> getConjuncts() {
        return conjuncts;
    }

//    /**
//     * Return the amount of disjuncts in the conjunct at the specified index.
//     * @param index of the conjunct in the genome
//     * @return the amount of disjuncts in the conjunct at the specified index
//     */
//    public int getConjunctSize(int index) {
//        if (index >= 0 && index < conjuncts.size()) {
//            return conjuncts.get(index).size();
//        }
//
//        return 0;
//    }

    public RandomAccessSet<LoopInvariantFreeGen> getRandomConjunct() {
        return conjuncts.getRandomElement();
    }

    /**
     * Adds the provided list of genes as a conjunct, where every element of that list represents a disjunct of a
     * disjunction.
     *
     * @param conjunct that is going to be added
     */
    public void addConjunct(RandomAccessSet<LoopInvariantFreeGen> conjunct) {
        RandomAccessSet<LoopInvariantFreeGen> newConjunct = new RandomAccessSet<>();
        for (LoopInvariantFreeGen disjunct : conjunct) {
            newConjunct.add(new LoopInvariantFreeGen(disjunct));
        }
        this.conjuncts.add(newConjunct);
        changedSinceCalc = true;
        containingTermsRefreshed = false;
    }

    /**
     * Adds the provided gen as its own conjunct into the genome.
     *
     * @param conjunct that is going to be added
     */
    public void addConjunct(LoopInvariantFreeGen conjunct) {
        RandomAccessSet<LoopInvariantFreeGen> newConjunct = new RandomAccessSet<>();
        newConjunct.add(conjunct);
        addConjunct(newConjunct);
    }

    public void removeRandomConjunct() {
        conjuncts.removeRandomElement();
    }

//    /**
//     * Removes the conjunct at the provided index.
//     * @param index of the conjunct that should be removed.
//     */
//    public void removeConjunct(int index) {
//        if (index >= 0 && index < conjuncts.size()) {
//            conjuncts.remove(index);
//            changedSinceCalc = true;
//            containingTermsRefreshed = false;
//        }
//
//    }

    /**
     * Flips the polarity of the conjunct at the provided index. Since the conjunct is a disjunction, the individual
     * disjuncts are negated and added as conjuncts into the genome, whereas the original conjunct is removed.
     */
    public void negateRandomConjunct() {
        RandomAccessSet<LoopInvariantFreeGen> removedConjunct = conjuncts.removeRandomElement();

        for (LoopInvariantFreeGen disjunct : removedConjunct) {
            disjunct.negate();
            addConjunct(disjunct);
        }

        changedSinceCalc = true;

    }

//    /**
//     * Add the provided disjunct into the disjunction under the conjunct at the provided index.
//     * @param disjunct that should be added
//     * @param index of the position of the new disjunct
//     */
//    public void addDisjunct(LoopInvariantFreeGen disjunct, int index) {
//        if (index >= 0 && index < conjuncts.size()) {
//            List<LoopInvariantFreeGen> conjunct = conjuncts.get(index);
//            conjunct.add(new LoopInvariantFreeGen(disjunct));
//            changedSinceCalc = true;
//            containingTermsRefreshed = false;
//        }
//
//    }

//    /**
//     * Removes the disjunct at the provided indices.
//     * @param conjunctIndex the index of the conjunct
//     * @param disjunctIndex the index of the disjunct in the specified conjunct
//     */
//    public void removeDisjunct(int conjunctIndex, int disjunctIndex) {
//        if (conjunctIndex >= 0 && conjunctIndex < conjuncts.size() &&
//                disjunctIndex >= 0 && disjunctIndex < conjuncts.get(conjunctIndex).size()) {
//
//            if (getConjunctSize(conjunctIndex) == 1) {
//                removeConjunct(conjunctIndex);
//            } else {
//                conjuncts.get(conjunctIndex).remove(disjunctIndex);
//            }
//            changedSinceCalc = true;
//            containingTermsRefreshed = false;
//        }
//    }

//    /**
//     * Flips the polarity of the disjunct under the provided indices.
//     * @param conjunctIndex the index of the conjunct
//     * @param disjunctIndex the index of the disjunct in the specified conjunct
//     */
//    public void negateDisjunct(int conjunctIndex, int disjunctIndex) {
//        if (conjunctIndex >= 0 && conjunctIndex < conjuncts.size() &&
//                disjunctIndex >= 0 && disjunctIndex < conjuncts.get(conjunctIndex).size()) {
//            conjuncts.get(conjunctIndex).get(disjunctIndex).negate();
//            changedSinceCalc = true;
//        }
//    }

//    /**
//     * Checks whether the genome contains the program variable {@code programVariable} in any of the disjuncts.
//     * @param programVariable that is being searched for
//     * @return true if the genome contains the provided variable, otherwise false
//     */
//    public boolean containsProgramVariable(LocationVariable programVariable) {
//        refreshProgramVariableNameMap();
//
//        if (programVariable == null) {
//            return false;
//        }
//        for (List<LoopInvariantFreeGen> conjunct : conjuncts) {
//            for (LoopInvariantFreeGen disjunct : conjunct) {
//                if (disjunct.containsProgramVariable(programVariable)) {
//                    return true;
//                }
//            }
//        }
//
//        return false;
//    }

    public boolean containsTerm(Term term) {
        refreshContainingTerms();

        if (term == null) {
            return false;
        }

        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
            for (LoopInvariantFreeGen disjunct : conjunct) {
                if (disjunct.containsTerm(term)) {
                    return true;
                }
            }
        }

        return false;
    }

//    /**
//     * Replaces any occurrence of a variable with the name {@code oldVariable} by the variable {@code newVariable}.
//     * @param oldVariableName the name of the variable that should be replaced
//     * @param oldVariableSort the sort of the variable that should be replaced
//     * @param newVariable the variable that replaces the specified old variable
//     */
//    public void replaceVariable(Name oldVariableName, Sort oldVariableSort, JAbstractSortedOperator newVariable) {
//        for (List<LoopInvariantFreeGen> conjunct: conjuncts) {
//            for (LoopInvariantFreeGen disjunct: conjunct) {
//                disjunct.replaceVariable(oldVariableName, oldVariableSort, newVariable);
//            }
//        }
//
//        nameMapRefreshed = false;
//        changedSinceCalc = true;
//    }

    public void replaceTerm(Term oldTerm, Term newTerm) {
        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
            for (LoopInvariantFreeGen disjunct : conjunct) {
                disjunct.replaceTerm(oldTerm, newTerm);
            }
        }

        containingTermsRefreshed = false;
        changedSinceCalc = true;
    }

//    public Map<Name, Sort> getProgramVariableNameMap() {
//        refreshProgramVariableNameMap();
//        return programVariableNameMap;
//    }

    public RandomAccessSet<Term> getContainingTerms() {
        refreshContainingTerms();
        return containingTerms;
    }


//    /**
//     * Queries all its contained disjuncts for their program variable name sets and sets the genome program variable
//     * name set to the union of all the queried sets.
//     */
//    private void refreshProgramVariableNameMap() {
//        if (nameMapRefreshed) {
//            return;
//        }
//
//        programVariableNameMap = new HashMap<>();
//        for (List<LoopInvariantFreeGen> conjunct : conjuncts) {
//            for (LoopInvariantFreeGen disjunct : conjunct) {
//                programVariableNameMap.putAll(disjunct.getProgramVariableNameMap());
//            }
//        }
//        nameMapRefreshed = true;
//    }

    private void refreshContainingTerms() {
        if (containingTermsRefreshed) {
            return;
        }

        containingTerms = new RandomAccessSet<>();

        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
            for (LoopInvariantFreeGen disjunct : conjunct) {
                containingTerms.addAll(disjunct.getContainingTerms());
            }
        }
        containingTermsRefreshed = true;
    }

    /**
     * Provides a copy of this genome that is not identical to this genome.
     *
     * @return the same, but non-identical genome
     */
    public LoopInvariantFreeGenome copy() {
        LoopInvariantFreeGenome newGenome = new LoopInvariantFreeGenome(services, verificationConditions);
        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
            RandomAccessSet<LoopInvariantFreeGen> newConjunct = new RandomAccessSet<>();
            for (LoopInvariantFreeGen disjunct : conjunct) {
                newConjunct.add(disjunct.copy());
            }
            newGenome.addConjunct(newConjunct);
        }

        return newGenome;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        int i = 0;
        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
            int j = 0;
            for (LoopInvariantFreeGen disjunct : conjunct) {
                sb.append(disjunct);
                if (j + 1 < conjunct.size()) {
                    sb.append(" OR");
                }
                sb.append("\n");
                j++;
            }
            if (i + 1 < conjuncts.size()) {
                sb.append("AND");
            }

            sb.append("\n");
            i++;
        }

        return sb.toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }

        if (!(obj instanceof LoopInvariantFreeGenome)) {
            return false;
        }

        return conjuncts.equals(((LoopInvariantFreeGenome) obj).conjuncts);
    }

    @Override
    public int hashCode() {
        return conjuncts.hashCode();
    }
}
