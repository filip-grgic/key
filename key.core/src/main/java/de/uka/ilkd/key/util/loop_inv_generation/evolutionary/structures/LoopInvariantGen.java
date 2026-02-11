package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures;

import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;

import java.util.*;

public abstract class LoopInvariantGen {

    protected boolean affirmative;
    protected Term term;
//    protected final Map<Name, Sort> programVariableNameMap;
    protected RandomAccessSet<Term> containingTerms;

    protected LoopInvariantGen() {
//        programVariableNameMap = new HashMap<>();
        containingTerms = new RandomAccessSet<>();
        affirmative = true;
    }

    /**
     * @return the non-negated term in the gen
     */
    public Term getTerm() {
        return term;
    }

    /**
     * Inverts the negation of the term that is represented by the gen.
     */
    public void negate() {
        affirmative = !affirmative;
    }

    /**
     * Signals, whether the term in the gen is negated or.
     * @return true, if there is a negation symbol, false otherwise
     */
    public boolean isNegated() {
        return !affirmative;
    }

    /**
     * Removes the negation and sets affirmative to false, in case term contains a negation as the highest operator.
     * Otherwise, the same term is returned back.
     * @param term the term that may or may not start with a negation
     * @return a non-negated term
     */
    protected Term extractedNonNegatedTerm(Term term) {
        affirmative = true;
        Term nonNegatedTerm = term;
        if (term.op().equals(Junctor.NOT)) {
            affirmative = false;
            nonNegatedTerm = term.sub(0);
        }

        return nonNegatedTerm;
    }

    public boolean containsTerm(Term term) {
        if (term == null) {
            return false;
        }

        return containingTerms.contains(term);
    }

    public Set<Term> getContainingTerms() {
        return containingTerms;
    }

    @Override
    public abstract boolean equals(Object obj);
}
