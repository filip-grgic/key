package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.TermSortCollector;
import de.uka.ilkd.key.util.loop_inv_generation.evolutionary.util.RandomAccessSet;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;

import java.util.ArrayList;
import java.util.List;

public class LoopInvariantFreeGen extends LoopInvariantGen {

    private final Services services;

    //TODO: include constants somehow

    public LoopInvariantFreeGen(Services services, Term term) {
        super();
        this.services = services;
        TermFactory termFactory = services.getTermFactory();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        Term clonedTerm = termFactory.createTerm((JTerm) term);

        // Check whether term is negated and save non-negated term
        Term nonNegatedTerm = extractedNonNegatedTerm(clonedTerm);

        if (nonNegatedTerm.op().equals(integerLDT.getGreaterThan())) {
            nonNegatedTerm = termFactory.createTerm(integerLDT.getLessThan(), (JTerm) nonNegatedTerm.sub(1), (JTerm) nonNegatedTerm.sub(0));
        } else if (nonNegatedTerm.op().equals(integerLDT.getGreaterOrEquals())) {
            nonNegatedTerm = termFactory.createTerm(integerLDT.getLessOrEquals(), (JTerm) nonNegatedTerm.sub(1), (JTerm) nonNegatedTerm.sub(0));
        }

        // Check whether the operator is < or <= as per normalisation
        if (!(nonNegatedTerm.op().equals(integerLDT.getLessThan()) || nonNegatedTerm.op().equals(integerLDT.getLessOrEquals()) ||
                nonNegatedTerm.op().equals(integerLDT.getGreaterThan()) ||  nonNegatedTerm.op().equals(integerLDT.getGreaterOrEquals()) ||
                nonNegatedTerm.op().name().toString().contains("equals"))) {
            throw new IllegalArgumentException(String.format("The operator in the non-negated term must be either \"less/greater than\", \"less/greater or equals\" or \"equals\", but is %s: %s ",
                    nonNegatedTerm.op(), nonNegatedTerm));
        }

        // Check whether the subterms are both integers
        Term left = nonNegatedTerm.sub(0);
        Term right = nonNegatedTerm.sub(1);
        Sort integerSort = services.getTypeConverter().getIntegerLDT().targetSort();

        if (!left.sort().equals(integerSort)) {
            throw new IllegalArgumentException(String.format("The left side is not an integer: %s", left));
        } else if (!right.sort().equals(integerSort)) {
            throw new IllegalArgumentException(String.format("The right side is not an integer: %s", right));
        }

        this.term = nonNegatedTerm;

        collectAllTerms();
    }

    public LoopInvariantFreeGen(LoopInvariantFreeGen other) {
        this(other.services, other.term);
        this.affirmative = other.affirmative;
    }

    /**
     * @return the left sub term of the gen's term
     */
    public Term getLeft() {
        return term.sub(0);
    }

    /**
     * @return the right sub term of the gen's term
     */
    public Term getRight() {
        return term.sub(1);
    }

    public Term translateToTerm() {
        TermBuilder termBuilder = services.getTermBuilder();
        TermFactory termFactory = services.getTermFactory();
        JTerm result = termFactory.createTerm((JTerm) term);

        if (!affirmative) {
            result = termBuilder.not(result);
        }

        return result;
    }

    private void collectAllTerms() {
        //Collect all integer terms
        containingTerms = new RandomAccessSet<>();
        TermSortCollector tsc = new TermSortCollector(services, false, false);
        term.execPostOrder(tsc);
        for (Sort sort : tsc.result().keySet()) {
            containingTerms.addAll(tsc.result().get(sort));
        }
    }

    public void replaceTerm(Term oldTerm, Term newTerm) {
        if (!oldTerm.sort().equals(newTerm.sort())) {
            return;
        }

        term = services.getTermBuilder().replaceContainingTerm(term, oldTerm, newTerm);
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof LoopInvariantFreeGen other)) {
            return false;
        } else if (this == obj) {
            return true;
        }

        return term.equals(other.term) && affirmative == other.affirmative;
    }

    @Override
    public int hashCode() {
        int hashCode = 11;
        hashCode = hashCode * 31 + term.hashCode();
        hashCode = hashCode * 31 + (affirmative ? 1 : 0);
        return hashCode;
    }

    public LoopInvariantFreeGen copy() {
        LoopInvariantFreeGen newGen = new LoopInvariantFreeGen(services, this.term);
        newGen.affirmative = affirmative;
        return newGen;
    }

    @Override
    public String toString() {
        return String.format("%s%s",
                this.affirmative ? "" : "NOT ", this.term);
    }
}
