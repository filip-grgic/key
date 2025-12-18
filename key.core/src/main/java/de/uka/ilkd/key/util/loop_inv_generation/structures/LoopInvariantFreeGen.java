package de.uka.ilkd.key.util.loop_inv_generation.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.HashSet;
import java.util.Set;

public class LoopInvariantFreeGen {

    private Term term;
    private boolean affirmative;
    private final Services services;
    private final Set<Name> programVariableNameSet;

    public LoopInvariantFreeGen(Services services, Term term) {
        this.services = services;
        this.programVariableNameSet = new HashSet<>();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        // Check whether term is negated and save non-negated term
        affirmative = true;
        Term nonNegatedTerm = term;
        if (term.op().equals(Junctor.NOT)) {
            affirmative = false;
            nonNegatedTerm = term.sub(0);
        }

        // Check whether the operator is < or <= as per normalisation
        if (!(nonNegatedTerm.op().equals(integerLDT.getLessThan()) || nonNegatedTerm.op().equals(integerLDT.getLessOrEquals()))) {
            throw new IllegalArgumentException(String.format("The operator in the non-negated term must be either \"less than\" or \"less or equals\", but is %s: %s ",
                    nonNegatedTerm.op(), nonNegatedTerm));
        }

        // Check whether the subterms are both integers
        Term left = nonNegatedTerm.sub(0);
        Term right = nonNegatedTerm.sub(1);
        Sort integerSort = services.getTypeConverter().getIntegerLDT().targetSort();

        if (!left.sort().equals(integerSort)) {
            throw new IllegalArgumentException(String.format("The left side is not an integer: %s", left));
        } else if (!right.sort().equals(integerSort)) {
            throw new IllegalArgumentException(String.format("The right side is not an integer: %s", right));
        }

        // Collect all program variables
        TermProgramVariableCollector pvc = new TermProgramVariableCollector(services);
        term.execPostOrder(pvc);
        programVariableNameSet.addAll(pvc.result().stream().map(LocationVariable::name).toList());

        this.term = nonNegatedTerm;
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
     * @return the non-negated term in the gen
     */
    public Term getTerm() {
        return term;
    }

    /**
     * @return the left sub term of the gen's term
     */
    public Term getLeft() {
        return term.sub(0);
    }

    /**
     * @return the right sub term of the gen's term
     */
    public Term getRight() {
        return term.sub(1);
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
    public void replaceProgramVariable(LocationVariable oldVariable, LocationVariable newVariable) {
        if (!containsProgramVariable(oldVariable) || oldVariable == null || newVariable == null) {
            return;
        }

        term = replaceProgramVariableInTerm(term, oldVariable.name(), newVariable);

        programVariableNameSet.remove(oldVariable.name());
        programVariableNameSet.add(newVariable.name());
    }

    private Term replaceProgramVariableInTerm(Term term, Name oldVariableName, LocationVariable newVariable) {

        if (term.op() instanceof LocationVariable && term.op().name().equals(oldVariableName)) {
            return services.getTermBuilder().var(newVariable);
        } else if (term.arity() == 0) {
            return term;
        }

        var oldSubs = term.subs();
        JTerm[] newSubs = new JTerm[oldSubs.size()];
        for (int i = 0; i < oldSubs.size(); i++) {
            //TODO: Handle subs being null
            newSubs[i] = (JTerm) replaceProgramVariableInTerm(oldSubs.get(i), oldVariableName, newVariable);
        }

        return services.getTermFactory().createTerm(term.op(), newSubs);
    }
}
