package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.util.loop_inv_generation.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.op.AbstractOperator;
import org.key_project.logic.sort.Sort;

import java.util.*;

public class TermSortCollector implements DefaultVisitor {

    private final Map<Sort, RandomAccessSet<Term>> result;
    private final Services services;
    private final List<Sort> allowedSorts;

    public TermSortCollector(Services services) {
        this.result = new LinkedHashMap<>();
        this.services = services;
        this.allowedSorts = new ArrayList<>();

        allowedSorts.add(services.getTypeConverter().getIntegerLDT().targetSort());
    }

    @Override
    public void visit(Term visited) {
        if (!allowedSorts.contains(visited.sort())) {
            return;
        }

        if (visited.op() instanceof AbstractOperator) {
            AbstractOperator op = (AbstractOperator) visited.op();
            if (op.name().toString().startsWith("result")) {
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
