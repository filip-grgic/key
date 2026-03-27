package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.logic.DefaultVisitor;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;

public class QuantifiableVariableVisitor implements DefaultVisitor {
    private boolean containsQuantifiableVariable = false;

    @Override
    public void visit(Term visited) {
        if (visited.op() instanceof QuantifiableVariable) {
            containsQuantifiableVariable = true;
        }
    }

    public boolean containsQuantifiableVariable() {
        return containsQuantifiableVariable;
    }
}
