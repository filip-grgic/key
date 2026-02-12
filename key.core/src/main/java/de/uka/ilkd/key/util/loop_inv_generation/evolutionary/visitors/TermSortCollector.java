package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.visitors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.op.AbstractOperator;
import org.key_project.logic.sort.Sort;

import java.util.*;

public class TermSortCollector implements DefaultVisitor {

    private final Map<Sort, RandomAccessSet<Term>> result;
    private final Services services;
    private final List<Sort> allowedSorts;
    private final boolean excludeReturnValue;
    private final boolean excludeConstants;

    public TermSortCollector(Services services) {
        this(services, true, true);
    }

    public TermSortCollector(Services services, boolean excludeReturnValue, boolean excludeConstants) {
        this.result = new LinkedHashMap<>();
        this.services = services;
        this.allowedSorts = new ArrayList<>();
        this.excludeReturnValue = excludeReturnValue;
        this.excludeConstants = excludeConstants;

        allowedSorts.add(services.getTypeConverter().getIntegerLDT().targetSort());
    }

    @Override
    public void visit(Term visited) {
        if (!allowedSorts.contains(visited.sort())) {
            return;
        }

        if (visited.op() instanceof AbstractOperator) {
            AbstractOperator op = (AbstractOperator) visited.op();
            if (excludeReturnValue && op.name().toString().startsWith("result_")) {
                return;
            } else if (excludeConstants && op.name().toString().equals("Z")) {
                return;
            }
        }

        if (!result.containsKey(visited.sort())) {
            result.put(visited.sort(), new RandomAccessSet<>());
        }

        result.get(visited.sort()).add(services.getTermFactory().createTerm((JTerm) visited));
    }

    public Map<Sort, RandomAccessSet<Term>> result() {
        return result;
    }
}
