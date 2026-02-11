package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.TermSortCollector;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

public class LoopInvariantLimitingGen extends LoopInvariantGen {

    private final Services services;
    private Term lowerLimit;
    private Term upperLimit;
    private LocationVariable variable;

    public LoopInvariantLimitingGen(Services services, LocationVariable variable, Term lowerLimit, Term upperLimit) {
        this.services = services;
        this.variable = variable;
        this.lowerLimit = lowerLimit;
        this.upperLimit = upperLimit;
    }

    public LoopInvariantLimitingGen(Services services, LoopInvariantLimitingGen other) {
        this(services, other.variable,
                services.getTermFactory().createTerm((JTerm) other.lowerLimit),
                services.getTermFactory().createTerm((JTerm) other.upperLimit));
    }

    @Override
    public Term getTerm() {
        Term result = null;
        TermBuilder tb = services.getTermBuilder();

        if (this.lowerLimit != null) {
            result = tb.leq((JTerm) lowerLimit, tb.var(variable));
        }

        if (this.upperLimit != null) {
            if (result == null) {
                result = tb.leq(tb.var(variable), (JTerm) upperLimit);
            } else {
                result = tb.and((JTerm) result, tb.leq(tb.var(variable), (JTerm) upperLimit));
            }
        }

        return result;
    }

    @Override
    public void replaceTerm(Term oldTerm, Term newTerm) {
        if (oldTerm.op().equals(variable) && newTerm.op() instanceof LocationVariable) {
            variable = (LocationVariable) newTerm.op();
        }

        TermBuilder tb = services.getTermBuilder();

        if (lowerLimit != null) {
            lowerLimit = tb.replaceContainingTerm(lowerLimit, oldTerm, newTerm);
        }

        if (upperLimit != null) {
            upperLimit = tb.replaceContainingTerm(upperLimit, oldTerm, newTerm);
        }
    }

    @Override
    protected void collectAllTerms() {
        //Collect all integer terms
        containingTerms = new RandomAccessSet<>();

        TermSortCollector tsc = new TermSortCollector(services, false, false);
        lowerLimit.execPostOrder(tsc);
        for (Sort sort : tsc.result().keySet()) {
            containingTerms.addAll(tsc.result().get(sort));
        }

        tsc = new TermSortCollector(services, true, false);
        upperLimit.execPostOrder(tsc);
        for (Sort sort : tsc.result().keySet()) {
            containingTerms.addAll(tsc.result().get(sort));
        }
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof LoopInvariantLimitingGen other)) {
            return false;
        } else if (this == obj) {
            return true;
        }

        return lowerLimit.equals(other.lowerLimit) && upperLimit.equals(other.upperLimit) && variable.equals(other.variable);
    }

    @Override
    public LoopInvariantGen copy() {
        return new LoopInvariantLimitingGen(services, this);
    }

    @Override
    public int hashCode() {
        int hashCode = 19;
        hashCode = hashCode * 37 + variable.hashCode();
        hashCode = hashCode * 37 + lowerLimit.hashCode();
        hashCode = hashCode * 37 + upperLimit.hashCode();
        return hashCode;
    }
}
