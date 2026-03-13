package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import org.key_project.logic.Term;

public class FreeConjunct extends Conjunct{
    private final Term term;

    public FreeConjunct(Term term, Services services) {
        super(services);
        this.term = term;
    }

    @Override
    public Term translateToTerm() {
        return term;
    }

    @Override
    public Conjunct replace(Term oldTerm, Term newTerm) {
        Term replacedTerm = services.getTermBuilder().replaceContainingTerm(term, oldTerm, newTerm);
        return new FreeConjunct(replacedTerm, services);
    }

    @Override
    public String toString() {
        return term.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        FreeConjunct that = (FreeConjunct) o;
        return term.equals(that.term);
    }

    @Override
    public int hashCode() {
        return 31 * term.hashCode();
    }
}
