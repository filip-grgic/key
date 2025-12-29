package de.uka.ilkd.key.util.loop_inv_generation.structures;

import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import org.key_project.logic.Name;
import org.key_project.logic.Term;

import java.util.HashSet;
import java.util.Set;

public abstract class LoopInvariantGen {

    protected boolean affirmative;
    protected Term term;
    protected final Set<Name> programVariableNameSet;

    protected LoopInvariantGen() {
        programVariableNameSet = new HashSet<>();
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

    /**
     * Checks whether the term in the gen contains the given program variable by checking whether the name exists
     * in the gen's variable namespace
     * @param programVariable that should be checked whether it is contained
     * @return true if there exists a variable with the same name in the gen, false if otherwise
     */
    public boolean containsProgramVariable(LocationVariable programVariable) {
        if (programVariable == null) {
            return false;
        }

        return programVariableNameSet.contains(programVariable.name());
    }

    /**
     * Replace all occurrences of oldVariable with newVariable in the term.
     * @param oldVariable the variable that should be replaced
     * @param newVariable the variable that should replace oldVariable
     */
    public abstract void replaceProgramVariable(LocationVariable oldVariable, LocationVariable newVariable);

    @Override
    public abstract boolean equals(Object obj);
}
