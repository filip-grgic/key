package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.DefaultVisitor;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.HashSet;
import java.util.LinkedHashSet;

public class FreeBinaryTermCollector implements DefaultVisitor {

    private final HashSet<Tuple<Term, Term>> result = new LinkedHashSet<>();

    @Override
    public void visit(Term visited) {
        if (visited.op().sort(new Sort[0]).equals(JavaDLTheory.FORMULA) && visited.op().arity() == 2) {
            QuantifiableVariableVisitor qfv = new QuantifiableVariableVisitor();
            visited.execPostOrder(qfv);
            if (!qfv.containsQuantifiableVariable()) {
                result.add(new Tuple<>(visited.subs().get(0), visited.subs().get(1)));
            }
        }
    }

    public HashSet<Tuple<Term, Term>> result() {
        return result;
    }
}
