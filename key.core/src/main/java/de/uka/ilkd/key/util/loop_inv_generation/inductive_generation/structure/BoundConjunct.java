package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.QuantifiableVariableVisitor;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Tuple;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;

import java.util.*;

public class BoundConjunct extends Conjunct {

    private List<Tuple<Quantifier, QuantifiableVariable>> quantifiers;
    private Map<Term, VariableBounds> bounds;
    private Term term;
    private Junctor topLevelJunctor;
    private Map<Operator, Operator> bindingOperatorsNegations;

    private BoundConjunct(Services services) {
        super(services);
    }

    public BoundConjunct(BoundConjunct boundConjunct) {
        super(boundConjunct.services);
        this.quantifiers = boundConjunct.quantifiers.stream().map(Tuple::new).toList();
        this.bounds = new HashMap<>();
        boundConjunct.bounds.forEach((k,v) -> this.bounds.put(k, new VariableBounds(v)));
        this.term = boundConjunct.term;
        this.topLevelJunctor = boundConjunct.topLevelJunctor;
        this.bindingOperatorsNegations = boundConjunct.bindingOperatorsNegations;
    }

    public BoundConjunct(Term term, Services services) {
        this(services);
        quantifiers = new ArrayList<>();

        Term currentTerm = term;

        while (currentTerm.op() instanceof Quantifier) {
            quantifiers.add(new Tuple<>((Quantifier) currentTerm.op(), currentTerm.boundVars().get(0)));
            currentTerm = currentTerm.subs().get(0);
        }

        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        bindingOperatorsNegations = new HashMap<>();
        bindingOperatorsNegations.put(integerLDT.getLessThan(), integerLDT.getGreaterOrEquals());
        bindingOperatorsNegations.put(integerLDT.getGreaterThan(), integerLDT.getLessOrEquals());
        bindingOperatorsNegations.put(integerLDT.getLessOrEquals(), integerLDT.getGreaterThan());
        bindingOperatorsNegations.put(integerLDT.getGreaterOrEquals(), integerLDT.getLessThan());
        bindingOperatorsNegations.put(Equality.EQUALS, null);

        bounds = new HashMap<>();

        if (currentTerm.op().equals(Junctor.IMP)) {
            topLevelJunctor = Junctor.IMP;
            handleBounds(currentTerm.sub(0));
            currentTerm = currentTerm.sub(1);
        } else if (currentTerm.op().equals(Junctor.AND)) {
            topLevelJunctor = Junctor.AND;
            handleBounds(currentTerm.sub(0));
            currentTerm = currentTerm.sub(1);
        } else if (currentTerm.op().equals(Junctor.OR)) {
            topLevelJunctor = Junctor.IMP;
            handleNegatedBounds(currentTerm.sub(0));
            currentTerm = currentTerm.sub(1);
        }

        this.term = currentTerm;

    }

    private void handleNegatedBounds(Term negatedRestrictor) {
        Stack<Term> stack = new Stack<>();
        stack.push(negatedRestrictor);
        TermBuilder tb = services.getTermBuilder();

        while (!stack.isEmpty()) {
            Term term = stack.pop();
            if (!bindingOperatorsNegations.containsKey(term.op())) {
                term.subs().forEach(stack::push);
                continue;
            }

            Term extractingTerm;
            if (term.op().equals(Equality.EQUALS)) {
                //TODO: Need to implement not equals but don't know how
                continue;
            } else {
                extractingTerm = tb.func((Function) bindingOperatorsNegations.get(term.op()), (JTerm) term.sub(0), (JTerm) term.sub(1));
            }
            extractBound(extractingTerm);
        }
    }

    private void handleBounds(Term restrictor) {
        Stack<Term> stack = new Stack<>();
        stack.push(restrictor);

        while (!stack.isEmpty()) {
            Term term = stack.pop();
            if (!bindingOperatorsNegations.containsKey(term.op())) {
                term.subs().forEach(stack::push);
                continue;
            }

            extractBound(term);
        }

    }

    private void extractBound(Term term) {
        Term preparedTerm = term;
        QuantifiableVariableVisitor qvv = new QuantifiableVariableVisitor();
        preparedTerm.sub(0).execPostOrder(qvv);

        boolean leftQuantified = qvv.containsQuantifiableVariable();

        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        TermBuilder tb = services.getTermBuilder();

        // Transform >/< into >=/<=
        if (preparedTerm.op().equals(integerLDT.getLessThan())) {
            preparedTerm = leftQuantified ?
                    tb.leq((JTerm) preparedTerm.sub(0), tb.func(integerLDT.getSub(), (JTerm) preparedTerm.sub(1), integerLDT.one())) :
                    tb.leq(tb.add((JTerm) preparedTerm.sub(0), integerLDT.one()), (JTerm) preparedTerm.sub(1));
        } else if (preparedTerm.op().equals(integerLDT.getGreaterThan())) {
            preparedTerm = leftQuantified ?
                    tb.geq((JTerm) preparedTerm.sub(0), tb.add((JTerm) preparedTerm.sub(1), integerLDT.one())) :
                    tb.geq(tb.func(integerLDT.getSub(), (JTerm) preparedTerm.sub(0), integerLDT.one()), (JTerm) preparedTerm.sub(1));
        }

        // If there is no quantified variable on the left, swap sides
        if (!leftQuantified) {
            if (preparedTerm.op().equals(Equality.EQUALS)) {
                preparedTerm = tb.equals((JTerm) preparedTerm.sub(1), (JTerm) preparedTerm.sub(0));
            } else if (preparedTerm.op().equals(integerLDT.getLessOrEquals())) {
                preparedTerm = tb.geq((JTerm) preparedTerm.sub(1), (JTerm) preparedTerm.sub(0));
            } else if (preparedTerm.op().equals(integerLDT.getGreaterOrEquals())) {
                preparedTerm = tb.leq((JTerm) preparedTerm.sub(1), (JTerm) preparedTerm.sub(0));
            }
        }

        // Create new bounds for the left side
        if (!bounds.containsKey(preparedTerm.sub(0))) {
            bounds.put(preparedTerm.sub(0), new VariableBounds(services));
        }

        VariableBounds variableBounds = bounds.get(preparedTerm.sub(0));

        if (preparedTerm.op().equals(Equality.EQUALS) || preparedTerm.op().equals(integerLDT.getLessOrEquals())) {
            variableBounds.addUpperBound(preparedTerm.sub(1));
        }

        if (preparedTerm.op().equals(Equality.EQUALS) || preparedTerm.op().equals(integerLDT.getGreaterOrEquals())) {
            variableBounds.addLowerBound(preparedTerm.sub(1));
        }
    }

    @Override
    public Term translateToTerm() {
        TermBuilder tb = services.getTermBuilder();
        Term result = term;

        Term restrictor = null;
        for (Term key : bounds.keySet()) {
            if (restrictor == null) {
                restrictor = bounds.get(key).setBounds(key);
            } else {
                restrictor = services.getTermBuilder().and((JTerm) restrictor, (JTerm) bounds.get(key).setBounds(key));
            }
        }

        if (restrictor != null) {
            if (topLevelJunctor.equals(Junctor.IMP)) {
                result = tb.imp((JTerm) restrictor, (JTerm) result);
            } else if (topLevelJunctor.equals(Junctor.AND)) {
                result = tb.and((JTerm) restrictor, (JTerm) result);
            }
        }

        for (int i = quantifiers.size() - 1; i >= 0; i--) {
            Tuple<Quantifier, QuantifiableVariable> quantifier = quantifiers.get(i);
            if (quantifier.first().equals(Quantifier.ALL)) {
                result = tb.all(quantifier.second(), (JTerm) result);
            } else if (quantifier.first().equals(Quantifier.EX)) {
                result = tb.ex(quantifier.second(), (JTerm) result);
            }
        }

        return result;
    }

    @Override
    public Conjunct replace(Term oldTerm, Term newTerm) {
        TermBuilder tb = services.getTermBuilder();
        BoundConjunct result = new BoundConjunct(services);
        result.quantifiers = new ArrayList<>(quantifiers);
        result.bounds = new HashMap<>();
        bounds.forEach((k, v) ->
                result.bounds.put(tb.replaceContainingTerm(k, oldTerm, newTerm), v.replace(oldTerm, newTerm)));
        result.term = tb.replaceContainingTerm(term, oldTerm, newTerm);
        result.topLevelJunctor = topLevelJunctor;
        return result;
    }

    public VariableBounds getBounds(Term boundedTerm) {
        return bounds.get(boundedTerm);
    }

    public Set<Term> getBoundedTerms() {
        return bounds.keySet();
    }

    @Override
    public String toString() {
        return translateToTerm().toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        BoundConjunct that = (BoundConjunct) o;
        return term.equals(that.term) &&
                quantifiers.equals(that.quantifiers) &&
                bounds.equals(that.bounds) &&
                topLevelJunctor.equals(that.topLevelJunctor);
    }

    @Override
    public int hashCode() {
        int result = 79;
        result = 31 * result + term.hashCode();
        result = 31 * result + quantifiers.hashCode();
        result = 31 * result + bounds.hashCode();
        result = 31 * result + topLevelJunctor.hashCode();
        return result;
    }
}
