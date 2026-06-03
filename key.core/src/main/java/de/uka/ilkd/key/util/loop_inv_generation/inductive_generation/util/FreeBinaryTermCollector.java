package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.DefaultVisitor;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

public class FreeBinaryTermCollector implements DefaultVisitor {

    private final Map<Tuple<Term, Term>, Operator> result = new HashMap<>();

    @Override
    public void visit(Term visited) {
        if (visited.op().sort(new Sort[0]).equals(JavaDLTheory.FORMULA) && visited.op().arity() == 2) {
            QuantifiableVariableVisitor qfv = new QuantifiableVariableVisitor();
            visited.execPostOrder(qfv);
            if (!qfv.containsQuantifiableVariable()) {
                result.put(new Tuple<>(visited.subs().get(0), visited.subs().get(1)), visited.op());
            }
        }
    }

    public Map<Tuple<Term, Term>, Operator> result() {
        return result;
    }
}
