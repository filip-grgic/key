package de.uka.ilkd.key.util.loop_inv_generation.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.JAbstractSortedOperator;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.AbstractSortedOperator;
import org.key_project.logic.sort.Sort;

public class LoopInvariantFreeGen extends LoopInvariantGen {

    private final Services services;

    //TODO: include constants somehow

    public LoopInvariantFreeGen(Services services, Term term) {
        super();
        this.services = services;
        TermFactory termFactory = services.getTermFactory();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        Term clonedTerm = termFactory.createTerm((JTerm) term);

        // Check whether term is negated and save non-negated term
        Term nonNegatedTerm = extractedNonNegatedTerm(clonedTerm);

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
        nonNegatedTerm.execPostOrder(pvc);
        programVariableNameSet.addAll(pvc.result().stream().map(LocationVariable::name).toList());

        this.term = nonNegatedTerm;
    }

    public LoopInvariantFreeGen(LoopInvariantFreeGen other) {
        this(other.services, other.term);
        this.affirmative = other.affirmative;
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

    public Term translateToTerm() {
        TermBuilder termBuilder = services.getTermBuilder();
        TermFactory termFactory = services.getTermFactory();
        JTerm result = termFactory.createTerm((JTerm) term);

        if (!affirmative) {
            result = termBuilder.not(result);
        }

        return result;
    }

    /**
     * Replace all occurrences of oldVariable with newVariable in the term.
     * @param oldVariable the variable that should be replaced
     * @param newVariable the variable that should replace oldVariable
     */
    @Override
    public void replaceVariable(LocationVariable oldVariable, AbstractSortedOperator newVariable) {
        if (oldVariable == null) {
            return;
        }
        replaceVariable(oldVariable.name(), newVariable);
    }

    @Override
    public void replaceVariable(Name oldVariableName, AbstractSortedOperator newVariable) {
        if (!containsProgramVariable(oldVariableName) || oldVariableName == null || newVariable == null) {
            return;
        }

        term = services.getTermBuilder().replaceVariable(term, oldVariableName, newVariable);

        programVariableNameSet.remove(oldVariableName);
        programVariableNameSet.add(newVariable.name());
    }


    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof LoopInvariantFreeGen other)) {
            return false;
        } else if (this == obj) {
            return true;
        }

        return term.equals(other.term) && affirmative == other.affirmative;
    }

    public LoopInvariantFreeGen copy() {
        LoopInvariantFreeGen newGen = new LoopInvariantFreeGen(services, this.term);
        newGen.affirmative = affirmative;
        return newGen;
    }

    @Override
    public String toString() {
        return String.format("%s%s",
                this.affirmative ? "NOT " : "", this.term);
    }
}
