package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.QuantifierCollector;
import org.key_project.logic.Term;

public abstract class Conjunct {

    protected Services services;

    public Conjunct(Services services) {
        this.services = services;
    }

    public abstract Term translateToTerm();

    public abstract Conjunct replace(Term oldTerm, Term newTerm);

    public abstract String toString();

    public abstract boolean equals(Object o);

    public abstract int hashCode();

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
