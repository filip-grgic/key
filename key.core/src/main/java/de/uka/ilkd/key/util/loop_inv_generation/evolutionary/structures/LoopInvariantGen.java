package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures;

import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;

import java.util.*;

public abstract class LoopInvariantGen {

    protected RandomAccessSet<Term> containingTerms;

    protected LoopInvariantGen() {
        containingTerms = new RandomAccessSet<>();
    }

    /**
     * @return the non-negated term in the gen
     */
    public abstract Term getTerm();

    public boolean containsTerm(Term term) {
        if (term == null) {
            return false;
        }

        return containingTerms.contains(term);
    }

    public Set<Term> getContainingTerms() {
        return containingTerms;
    }

    public abstract void replaceTerm(Term oldTerm, Term newTerm);

    protected abstract void collectAllTerms();

    @Override
    public abstract boolean equals(Object obj);

    public abstract LoopInvariantGen copy();

    @Override
    public abstract int hashCode();
}
