package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import org.key_project.logic.Named;
import org.key_project.logic.Term;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class NamedVariableCollector implements DefaultVisitor {

    private final List<String> names;
    private final Map<String, Term> result = new HashMap<>();

    public NamedVariableCollector(List<String> names) {
        this.names = names;
    }

    @Override
    public void visit(Term visited) {
        if (visited.subs().isEmpty() && names.contains(visited.op().name().toString())) {
            result.put(visited.op().name().toString(), visited);
        }
    }

    public Map<String, Term> result() {
        return result;
    }
}
