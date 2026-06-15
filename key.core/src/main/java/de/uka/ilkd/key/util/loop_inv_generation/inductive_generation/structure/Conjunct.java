package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.QuantifierCollector;
import org.key_project.logic.Term;

public abstract class Conjunct {

    protected Services services;

    public Conjunct(Services services) {
        this.services = services;
    }

    /**
     * Translate the conjunct to a term for KeY.
     * @return Term representing the conjunct
     */
    public abstract Term translateToTerm();

    /**
     * Replace oldTerm in the conjunct with newTerm.
     * @param oldTerm term to be replaced
     * @param newTerm term to replace with
     * @return conjunct with replaced term
     */
    public abstract Conjunct replace(Term oldTerm, Term newTerm);

    /**
     * Creates and returns a String representation of the conjunct.
     * @return String representation of the conjunct
     */
    public abstract String toString();

    public abstract boolean equals(Object o);

    public abstract int hashCode();

    /**
     * Creates a simple conjunct from a term.
     * Creates a BoundConjunct if the term contains quantifiers, otherwise creates a FreeConjunct.
     * @param term term to be converted to conjunct
     * @param services services to be used
     * @return the created conjunct
     */
    public static Conjunct create(Term term, Services services) {
        QuantifierCollector qc = new QuantifierCollector();
        term.execPostOrder(qc);

        if (qc.containsQuantifier()) {
            return new BoundConjunct(term, services);
        } else {
            return new FreeConjunct(term, services);
        }
    }

}
