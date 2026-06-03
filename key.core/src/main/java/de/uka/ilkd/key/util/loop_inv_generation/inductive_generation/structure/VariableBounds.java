package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import org.key_project.logic.Term;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class VariableBounds {

    private final Set<Term> lowerBounds;
    private final Set<Term> upperBounds;
    private final Set<Term> exclusiveLowerBounds = new HashSet<>();
    private final Set<Term> exclusiveUpperBounds = new HashSet<>();
    private final Services services;

    public VariableBounds(Services services) {
        this.services = services;
        this.lowerBounds = new HashSet<>();
        this.upperBounds = new HashSet<>();
    }

    public VariableBounds(VariableBounds variableBounds) {
        this.services = variableBounds.services;
        this.lowerBounds = new HashSet<>(variableBounds.lowerBounds);
        this.upperBounds = new HashSet<>(variableBounds.upperBounds);
    }

    public Set<Term> getLowerBounds() {
        return lowerBounds;
    }

    public Set<Term> getUpperBounds() {
        return upperBounds;
    }

    public Set<Term> getExclusiveLowerBounds() {
        return exclusiveLowerBounds;
    }

    public Set<Term> getExclusiveUpperBounds() {
        return exclusiveUpperBounds;
    }

    public Set<Term> getAllLowerBounds() {
        Set<Term> result = new HashSet<>(lowerBounds);
        result.addAll(exclusiveLowerBounds);
        return result;
    }

    public Set<Term> getAllUpperBounds() {
        Set<Term> result = new HashSet<>(upperBounds);
        result.addAll(exclusiveUpperBounds);
        return result;
    }

    public void addLowerBound(Term bound) {
        checkInteger(bound, "Lower bound must be an integer");
        lowerBounds.add(bound);
        exclusiveLowerBounds.add(subtractOne(bound));
    }

    public void addUpperBound(Term bound) {
        checkInteger(bound, "Upper bound must be an integer");
        upperBounds.add(bound);
        exclusiveUpperBounds.add(addOne(bound));
    }

    public void addExclusiveLowerBound(Term bound) {
        checkInteger(bound, "Lower bound must be an integer");
        exclusiveLowerBounds.add(bound);
        lowerBounds.add(addOne(bound));
    }

    public void addExclusiveUpperBound(Term bound) {
        checkInteger(bound, "Upper bound must be an integer");
        exclusiveUpperBounds.add(bound);
        upperBounds.add(subtractOne(bound));
    }

    private Term addOne(Term term) {
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        TermBuilder tb = services.getTermBuilder();
        Term negOne = tb.neg(tb.one());
        if (term.op().equals(integerLDT.getAdd())) {
            if (term.sub(0).equals(negOne)) {
                return term.sub(1);
            } else if (term.sub(1).equals(negOne)) {
                return term.sub(0);
            }
        } else if (term.op().equals(integerLDT.getSub())) {
            if (term.sub(1).equals(tb.one())) {
                return term.sub(0);
            }
        }
        return tb.add((JTerm) term, tb.one());
    }

    private Term subtractOne(Term term) {
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        TermBuilder tb = services.getTermBuilder();
        Term negOne = tb.neg(tb.one());
        if (term.op().equals(integerLDT.getAdd())) {
            if (term.sub(0).equals(tb.one())) {
                return term.sub(1);
            } else if (term.sub(1).equals(tb.one())) {
                return term.sub(0);
            }
        } else if (term.op().equals(integerLDT.getSub())) {
            if (term.sub(1).equals(negOne)) {
                return term.sub(0);
            }
        }
        return tb.sub((JTerm) term, tb.one());
    }

    public void removeLowerBound() {
        this.lowerBounds.clear();
    }

    public void removeUpperBound() {
        this.upperBounds.clear();
    }

    public void replaceLowerBound(Term bound, boolean exclusive) {
        checkInteger(bound, "Lower bound must be an integer");
        removeLowerBound();
        if (exclusive) {
            addExclusiveLowerBound(bound);
        } else {
            addLowerBound(bound);
        }
    }

    public void replaceUpperBound(Term bound, boolean exclusive) {
        checkInteger(bound, "Upper bound must be an integer");
        removeUpperBound();
        if (exclusive) {
            addExclusiveUpperBound(bound);
        } else {
            addUpperBound(bound);
        }
    }

    public Term setBounds(Term term) {
        checkInteger(term, "Term for bounds must be an integer");
        TermBuilder tb = services.getTermBuilder();
        List<Term> boundedTerms = new ArrayList<>();
        for (Term lowerBound : lowerBounds) {
            boundedTerms.add(tb.leq((JTerm) lowerBound, (JTerm) term));
        }
        for (Term upperBound : upperBounds) {
            boundedTerms.add(tb.leq((JTerm) term, (JTerm) upperBound));
        }

        Term result = null;
        for (Term boundedTerm : boundedTerms) {
            if (result == null) {
                result = boundedTerm;
            } else {
                result = tb.and((JTerm) result, (JTerm) boundedTerm);
            }
        }

        return result;
    }

    public VariableBounds replace(Term oldTerm, Term newTerm) {
        VariableBounds result = new VariableBounds(services);
        lowerBounds.forEach(bound -> result.lowerBounds.add(services.getTermBuilder().replaceContainingTerm(bound, oldTerm, newTerm)));
        upperBounds.forEach(bound -> result.upperBounds.add(services.getTermBuilder().replaceContainingTerm(bound, oldTerm, newTerm)));
        return result;
    }

    private void checkInteger(Term term, String message) {
        if (!term.sort().equals(services.getTypeConverter().getIntegerLDT().targetSort())) {
            throw new IllegalArgumentException(message);
        }
    }

    public VariableBounds combine(VariableBounds other) {
        VariableBounds result = new VariableBounds(services);
        result.lowerBounds.addAll(lowerBounds);
        result.upperBounds.addAll(upperBounds);
        result.lowerBounds.addAll(other.lowerBounds);
        result.upperBounds.addAll(other.upperBounds);
        return result;
    }

    public static VariableBounds combine(VariableBounds... variableBounds) {
        VariableBounds result = variableBounds[0];
        for (int i = 1; i < variableBounds.length; i++) {
            result = result.combine(variableBounds[i]);
        }
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        VariableBounds that = (VariableBounds) obj;
        return lowerBounds.equals(that.lowerBounds) && upperBounds.equals(that.upperBounds);
    }
}
