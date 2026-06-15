package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.LoopInvariantFreeGenomeComparator;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.VerificationCondition;
import org.key_project.logic.Term;

import java.util.*;

public class LoopInvariantFreeGenome {

    private static LoopInvariantFreeGenomeComparator comparator;

    //    private final RandomAccessSet<RandomAccessSet<LoopInvariantFreeGen>> conjuncts;
    private final List<List<LoopInvariantFreeGen>> postconditions;
    private final Map<LocationVariable, LoopInvariantLimitingGen> limitingGens;
    private final Services services;
    private double fitness;
    private boolean changedSinceCalc;
    private boolean isSolution;
    //    private Map<Name, Sort> programVariableNameMap;
    private RandomAccessSet<Term> containingTerms;
    private boolean containingTermsRefreshed;
    private final VerificationCondition[] verificationConditions;
    private Set<VerificationCondition> validVerificationConditions;
    private Set<VerificationCondition> nonvalidVerificationConditions;
    private Term returnValue = null;

    public static LoopInvariantFreeGenomeComparator getComparator() {
        if (comparator == null) {
            comparator = new LoopInvariantFreeGenomeComparator();
        }
        return comparator;
    }

    private LoopInvariantFreeGenome(Services services,
                                    VerificationCondition[] verificationConditions) {
        this(services, verificationConditions, new ArrayList<>());
        assert this.postconditions.isEmpty();
    }

    public LoopInvariantFreeGenome(Services services,
                                   VerificationCondition[] verificationConditions,
                                   List<Term> postconditions) {
        this.services = services;
//        this.conjuncts = new RandomAccessSet<>();
        this.postconditions = extractPostconditions(postconditions);
        this.limitingGens = new HashMap<>();
        this.verificationConditions = verificationConditions;
//        programVariableNameMap =  new HashMap<>();
        containingTermsRefreshed = false;
        changedSinceCalc = true;
        validVerificationConditions = new HashSet<>();
        nonvalidVerificationConditions = new HashSet<>();
    }

    private List<List<LoopInvariantFreeGen>> extractPostconditions(List<Term> postconditions) {
        List<List<LoopInvariantFreeGen>> result = new ArrayList<>();

        for (Term postcondition : postconditions) {
            List<LoopInvariantFreeGen> genes = new ArrayList<>();
            Queue<Term> queue = new LinkedList<>();
            queue.add(postcondition);

            while (!queue.isEmpty()) {
                Term currentTerm = queue.poll();

                if (currentTerm.op().name().toString().equals("or")) {
                    queue.add(currentTerm.sub(0));
                    queue.add(currentTerm.sub(1));
                } else {
                    genes.add(new LoopInvariantFreeGen(services, currentTerm));
                }
            }

            result.add(genes);
        }

        return result;
    }

    public LoopInvariantFreeGenome(Services services) {
        this(services, new VerificationCondition[0], new ArrayList<>());
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

        fitness = 1;

//        //TODO: Try different Fitness strategies: e.g. weighted VCs depending on how many generations they have been fulfilled
//        isSolution = true;
//        for (VerificationCondition vc : verificationConditions) {
//            if (!vc.checkFulfillment(this)) {
//                fitness += 1;
//                isSolution = false;
//                nonvalidVerificationConditions.add(vc);
//            } else {
//                validVerificationConditions.add(vc);
//            }
//        }

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
        for (List<LoopInvariantFreeGen> conjunct : postconditions) {
            Term disjunction = null;
            for (LoopInvariantFreeGen disjunct : conjunct) {
                if (disjunction == null) {
                    disjunction = disjunct.getTerm();
                } else {
                    disjunction = termBuilder.or((JTerm) disjunction, (JTerm) disjunct.getTerm());
                }
            }

            if (conjunction == null) {
                conjunction = disjunction;
            } else {
                conjunction = termBuilder.and((JTerm) conjunction, (JTerm) disjunction);
            }
        }

        for (LocationVariable variableKey : limitingGens.keySet()) {
            LoopInvariantLimitingGen limitingGen = limitingGens.get(variableKey);
            if (conjunction == null) {
                conjunction = limitingGen.getTerm();
            } else {
                conjunction = termBuilder.and((JTerm) limitingGen.getTerm(), (JTerm) conjunction);
            }
        }

        if (conjunction == null) {
            conjunction = termBuilder.tt();
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

        if (other == null) {
            result.postconditions.addAll(this.postconditions);
            return result;
        }

        assert this.postconditions.size() == other.postconditions.size();

        Random random = new Random();

        for (int i = 0; i < this.postconditions.size(); i++) {
            if (random.nextBoolean()) {
                result.postconditions.add(this.postconditions.get(i));
            } else {
                result.postconditions.add(other.postconditions.get(i));
            }
        }

        Set<LocationVariable> keys = new HashSet<>(this.limitingGens.keySet());
        keys.addAll(other.limitingGens.keySet());

        for (LocationVariable key : keys) {
            LoopInvariantFreeGenome chosenGenome = (random.nextBoolean()) ? this : other;

            if (chosenGenome.limitingGens.containsKey(key)) {
                result.limitingGens.put(key, chosenGenome.limitingGens.get(key));
            }
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
        return postconditions.size() + limitingGens.size();
    }

    public List<List<LoopInvariantFreeGen>> getPostconditions() {
        return postconditions;
    }

    public List<LoopInvariantFreeGen> getRandomPostcondition() {
        Random random = new Random();
        int index = random.nextInt(postconditions.size());
        return postconditions.get(index);
    }

    public void addLimitingGen(LoopInvariantLimitingGen gen) {
        limitingGens.put(gen.getVariable(), gen);
    }

    public Map<LocationVariable, LoopInvariantLimitingGen> getLimitingGenes() {
        return limitingGens;
    }

    /**
     * Adds the provided list of genes as a conjunct, where every element of that list represents a disjunct of a
     * disjunction.
     *
     * @param postcondition that is going to be added
     */
    public void addPostcondition(List<LoopInvariantFreeGen> postcondition) {
        List<LoopInvariantFreeGen> newConjunct = new ArrayList<>();
        for (LoopInvariantFreeGen disjunct : postcondition) {
            newConjunct.add(new LoopInvariantFreeGen(disjunct));
        }
        this.postconditions.add(newConjunct);
        changedSinceCalc = true;
        containingTermsRefreshed = false;
    }

    /**
     * Adds the provided gen as its own postcondition into the genome.
     *
     * @param postcondition that is going to be added
     */
    public void addPostcondition(LoopInvariantFreeGen postcondition) {
        List<LoopInvariantFreeGen> newPostcondition = new ArrayList<>();
        newPostcondition.add(postcondition);
        this.addPostcondition(newPostcondition);
    }

    public List<LoopInvariantFreeGen> removeRandomConjunct() {
        Random random = new Random();
        int index = random.nextInt(postconditions.size());
        return postconditions.remove(index);
    }

    /**
     * Flips the polarity of the conjunct at the provided index. Since the conjunct is a disjunction, the individual
     * disjuncts are negated and added as conjuncts into the genome, whereas the original conjunct is removed.
     */
    private void negateRandomConjunct() {
        List<LoopInvariantFreeGen> removedConjunct = removeRandomConjunct();

        for (LoopInvariantFreeGen disjunct : removedConjunct) {
            disjunct.negate();
            addPostcondition(disjunct);
        }

        changedSinceCalc = true;

    }

    public boolean containsReturnValue() {
        refreshContainingTerms();
        return returnValue != null;
    }

    public Term getReturnValue() {
        return returnValue;
    }

    public boolean containsTerm(Term term) {
        refreshContainingTerms();

        if (term == null) {
            return false;
        }

        for (List<LoopInvariantFreeGen> postcondition : postconditions) {
            for (LoopInvariantFreeGen disjunct : postcondition) {
                if (disjunct.containsTerm(term)) {
                    return true;
                }
            }
        }

        return false;
    }

    public void replaceTerm(Term oldTerm, Term newTerm) {
        for (List<LoopInvariantFreeGen> postcondition : postconditions) {
            for (LoopInvariantFreeGen disjunct : postcondition) {
                disjunct.replaceTerm(oldTerm, newTerm);
            }
        }

        limitingGens.forEach((key, gen) -> gen.replaceTerm(oldTerm, newTerm));

        if (oldTerm.op().name().equals(returnValue.op().name())) {
            if (newTerm.op().name().toString().startsWith("result_")) {
                returnValue = newTerm;
            } else {
                returnValue = null;
            }
        }

        containingTermsRefreshed = false;
        changedSinceCalc = true;
    }

    public RandomAccessSet<Term> getContainingTerms() {
        refreshContainingTerms();
        return containingTerms;
    }

    private void refreshContainingTerms() {
        if (containingTermsRefreshed) {
            return;
        }

        containingTerms = new RandomAccessSet<>();

        List<LoopInvariantGen> genes = new ArrayList<>();

        for (List<LoopInvariantFreeGen> postcondition : postconditions) {
            genes.addAll(postcondition);
        }

        limitingGens.forEach((key, gen) -> genes.add(gen));

        for (LoopInvariantGen gen : genes) {
            containingTerms.addAll(gen.getContainingTerms());

            if (returnValue == null) {
                for (Term containingTerm : gen.getContainingTerms()) {
                    if (containingTerm.op().name().toString().startsWith("result_")) {
                        returnValue = containingTerm;
                        break;
                    }
                }
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
        for (List<LoopInvariantFreeGen> postcondition : postconditions) {
            List<LoopInvariantFreeGen> newConjunct = new ArrayList<>();
            for (LoopInvariantFreeGen disjunct : postcondition) {
                newConjunct.add(((LoopInvariantFreeGen) disjunct.copy()));
            }
            newGenome.addPostcondition(newConjunct);
        }

        for (LocationVariable locationVariable : limitingGens.keySet()) {
            newGenome.limitingGens.put(locationVariable,
                    (LoopInvariantLimitingGen) limitingGens.get(locationVariable).copy());
        }

        return newGenome;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append("Limiting Genes:\n");
        for (LocationVariable locationVariable : limitingGens.keySet()) {
            sb.append(String.format("\t%s: %s\n", locationVariable.name(), limitingGens.get(locationVariable)));
        }

        sb.append("\nPostconditions\n");
        int i = 0;
        for (List<LoopInvariantFreeGen> postcondition : postconditions) {
            int j = 0;
            for (LoopInvariantFreeGen disjunct : postcondition) {
                sb.append(disjunct);
                if (j + 1 < postcondition.size()) {
                    sb.append(" OR");
                }
                sb.append("\n");
                j++;
            }
            if (i + 1 < postconditions.size()) {
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

        LoopInvariantFreeGenome other = (LoopInvariantFreeGenome) obj;

        if (!this.limitingGens.keySet().equals(other.limitingGens.keySet())) {
            return false;
        }

        for (LocationVariable locationVariable : limitingGens.keySet()) {
            if (!this.limitingGens.get(locationVariable).equals(other.limitingGens.get(locationVariable))) {
                return false;
            }
        }

        if (this.postconditions.size() != other.postconditions.size()) {
            return false;
        }

        for (int i = 0; i < postconditions.size(); i++) {

            if (this.postconditions.get(i).size() != other.postconditions.get(i).size()) {
                return false;
            }

            for (int j = 0; j < postconditions.get(i).size(); j++) {
                if (this.postconditions.get(i).get(j) != other.postconditions.get(i).get(j)) {
                    return false;
                }

                if (!postconditions.get(i).get(j).equals(other.postconditions.get(i).get(j))) {
                    return false;
                }
            }
        }

        return true;
    }

    @Override
    public int hashCode() {
        int hashCode = 67;
        hashCode = hashCode * 73 + limitingGens.hashCode();
        hashCode = hashCode * 73 + postconditions.hashCode();
        return hashCode;
    }
}
