package de.uka.ilkd.key.util.loop_inv_generation.evolutionary;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.LabeledTermImpl;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;

import java.util.*;

public class EnsuresTermCollector implements DefaultVisitor {

    private final HashSet<Term> result = new LinkedHashSet<>();
    //    //TODO: Need to incorporate quantors
    private Services services;

    public EnsuresTermCollector(Services services) {
        this.services = services;
    }

    @Override
    public void visit(Term visited) {

        if (visited instanceof LabeledTermImpl labeledVisited) {
            for (TermLabel label : labeledVisited.getLabels()) {
                if (!(label instanceof OriginTermLabel)) {
                    continue;
                }

                if (label.toString().contains("ensures")) {
                    BinaryTermCollector btc = new BinaryTermCollector(services);
                    visited.execPostOrder(btc);
                    result.addAll(btc.result());
                }
            }
        }

    }

    public HashSet<Term> result() {
        return result;
    }
}
