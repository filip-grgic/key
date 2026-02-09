package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.EvolutionEngineParameters;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.LoopInvariantFreeGenomeComparator;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
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
    private Set<VerificationCondition> validVerificationConditions;
    private Set<VerificationCondition> nonvalidVerificationConditions;
    private Term returnValue = null;

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
        validVerificationConditions = new HashSet<>();
        nonvalidVerificationConditions = new HashSet<>();
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
        isSolution = true;
        for (VerificationCondition vc : verificationConditions) {
            if (!vc.checkFulfillment(this)) {
                fitness += 1;
                isSolution = false;
                nonvalidVerificationConditions.add(vc);
            } else {
                validVerificationConditions.add(vc);
            }
        }

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

    static public LoopInvariantFreeGenome generateRandomGenome(EvolutionEngineParameters parameters,
                                                               Services services) {
        Map<Sort, RandomAccessSet<Term>> termSorts = parameters.getTermSortSet();
        RandomAccessSet<Term> integerTerms = termSorts.get(services.getTypeConverter().getIntegerLDT().targetSort());

        Random random = new Random();

        TermBuilder termBuilder = services.getTermBuilder();
        Term left = integerTerms.getRandomElement();
        Term right = integerTerms.getRandomElement();

        Term randomTerm = switch (random.nextInt(5)) {
            case 0 -> termBuilder.lt((JTerm) left, (JTerm) right);
            case 1 -> termBuilder.leq((JTerm) left, (JTerm) right);
            case 2 -> termBuilder.gt((JTerm) left, (JTerm) right);
            case 3 -> termBuilder.geq((JTerm) left, (JTerm) right);
            case 4 -> termBuilder.equals((JTerm) left, (JTerm) right);
            default -> null;
        };

        assert randomTerm != null;

        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, randomTerm);
        LoopInvariantFreeGenome genome = new  LoopInvariantFreeGenome(services, parameters.getVerificationConditions());
        genome.addConjunct(gen);
        return genome;
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

        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
            for (LoopInvariantFreeGen disjunct : conjunct) {
                if (disjunct.containsTerm(term)) {
                    return true;
                }
            }
        }

        return false;
    }

    public void replaceTerm(Term oldTerm, Term newTerm) {
        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
            for (LoopInvariantFreeGen disjunct : conjunct) {
                disjunct.replaceTerm(oldTerm, newTerm);
            }
        }

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

        for (RandomAccessSet<LoopInvariantFreeGen> conjunct : conjuncts) {
            for (LoopInvariantFreeGen disjunct : conjunct) {
                containingTerms.addAll(disjunct.getContainingTerms());

                if (returnValue == null) {
                    for (Term containingTerm : disjunct.getContainingTerms()) {
                        if (containingTerm.op().name().toString().startsWith("result_")) {
                            returnValue = containingTerm;
                            break;
                        }
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
