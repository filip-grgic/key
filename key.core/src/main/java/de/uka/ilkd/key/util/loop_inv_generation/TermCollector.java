package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.op.*;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;

import java.util.*;

public class TermCollector implements DefaultVisitor {

    private final HashSet<Term> result = new LinkedHashSet<>();
    private final HashMap<Term, List<Term>> parentsMap = new HashMap<>();
    private final List<Class<? extends Operator>> allowedOperators = Arrays.asList(
            Junctor.class, Quantifier.class, Equality.class, JFunction.class, SortDependingFunction.class
    );
    private final List<Class<? extends Operator>> forbiddenOperators = Arrays.asList(
         JModality.class, UpdateApplication.class
    );

    @Override
    public void visit(Term visited) {

        if (forbiddenOperators.contains(visited.op().getClass())) {
            // Should purge all occurrences of the defined operators from the result
            removeAncestors(visited);
        } else if (allowedOperators.contains(visited.op().getClass())) {
            result.add(visited);
        }
        // Operators that are not present in either forbiddenOperators or allowedOperators (like LogicVariable or
        // ProgramVariable) are allowed to exist as a subterm but should not be added as a singular term in the result


        // Add new parent child relations to the parentsMap
        for (int i = 0; i < visited.subs().size(); i++) {
            if (!parentsMap.containsKey(visited.sub(i))) {
                parentsMap.put(visited.sub(i), new ArrayList<>());
            }
            parentsMap.get(visited.sub(i)).add(visited);
        }
    }

    public HashSet<Term> result() {
        return result;
    }

    private void removeAncestors(Term term) {
        List<Term> parents = parentsMap.get(term);
        if (parents != null) {
            for (Term parent : parents) {
                removeAncestors(parent);
                result.remove(parent);
            }
        }
    }
}
