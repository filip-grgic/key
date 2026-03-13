package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.op.Quantifier;
import org.key_project.logic.Term;

public class QuantifierCollector implements DefaultVisitor {
    private boolean containsQuantifier = false;

    @Override
    public void visit(Term visited) {
        if (visited.op().equals(Quantifier.ALL) || visited.op().equals(Quantifier.EX)) containsQuantifier = true;
    }

    public boolean containsQuantifier() {
        return containsQuantifier;
    }
}
