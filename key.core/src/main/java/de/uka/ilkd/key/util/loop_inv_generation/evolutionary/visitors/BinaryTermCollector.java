package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.visitors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.HashSet;
import java.util.LinkedHashSet;

public class BinaryTermCollector implements DefaultVisitor {

    private final HashSet<Term> result = new LinkedHashSet<>();
    private final Services services;
    private final TermFactory termFactory;

    public BinaryTermCollector(Services services) {
        this.services = services;
        this.termFactory = services.getTermFactory();
    }

    @Override
    public void visit(Term visited) {
        Sort integerSort = services.getTypeConverter().getIntegerLDT().targetSort();

        if (visited.op().name().toString().equals("leq") || visited.op().name().toString().equals("le") ||
                visited.op().name().toString().equals("geq") || visited.op().name().toString().equals("ge") ||
                visited.op().name().toString().equals("equals")) {
            Term left = visited.sub(0);
            Term right = visited.sub(1);

            if (left.sort().equals(integerSort) && right.sort().equals(integerSort)) {
                result.add(termFactory.createTerm((JTerm) visited));
            }
        }
    }

    public HashSet<Term> result() {
        return result;
    }
}
