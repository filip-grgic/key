package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import java.util.HashMap;
import java.util.Map;

public class SMTTranslator {

    private Services services;
    private final IntegerLDT integerLDT;
    private final TermBuilder termBuilder;

    private final static String LENGTH_FUNCTION = "length";
    private final static String ARR_FUNCTION = "arr";

    public SMTTranslator(Services services) {
        this.services = services;
        this.integerLDT = services.getTypeConverter().getIntegerLDT();
        this.termBuilder = services.getTermBuilder();
    }
    
    public String translateSequent(Sequent sequent) {
        if (sequent == null) {
            throw new IllegalArgumentException("Sequent cannot be null");
        }

        Map<String, String> declarations = new HashMap<>(); 
        StringBuilder problemBuilder = new StringBuilder();

        addInitDeclarations(declarations);


        // Translate antecedent
        for (SequentFormula formula : sequent.antecedent().asList()) {
            translateAssertion(formula.formula(), declarations, problemBuilder);
        }

        // Translate succedent (negating them)
        for (SequentFormula formula : sequent.succedent().asList()) {
            translateAssertion(
                    termBuilder.not((JTerm) formula.formula()),
                    declarations,
                    problemBuilder
            );
        }

        StringBuilder result = new StringBuilder();

        result.append("(set-option :produce-models true)\n\n");
        result.append("(set-logic AUFNIRA)\n");

        declarations.forEach((key, value) -> result.append(value));

        result.append("\n").append(problemBuilder).append("\n");
        result.append("(check-sat)\n");
        result.append("(get-value (");
        declarations.forEach((key, value) -> {
            if (value.contains("()")) {
                result.append(key).append(" ");
            }
        });
        result.append("))\n");

        return result.toString();
    }

    private void addInitDeclarations(Map<String, String> declarations) {
        // Add declaration for the length of array function
        declarations.put(LENGTH_FUNCTION, String.format("(declare-fun %s ((Array Int Int)) Int)\n", LENGTH_FUNCTION));
    }

    public void translateAssertion(Term term, Map<String, String> declarations, StringBuilder problemBuilder) {
        if (term == null) {
            throw new IllegalArgumentException("Term cannot be null");
        }

        // Recursively translate the term into an SMT-LIB formula
        problemBuilder.append("(assert ");
        recursiveTranslate(term, declarations, problemBuilder);
        problemBuilder.append(")\n");
    }

    private void recursiveTranslate(Term term, Map<String, String> declarations, StringBuilder problemBuilder) {
        // Base case: If the term is a constant or variable, append its SMT representation
        if (term.subs().isEmpty()) {
            problemBuilder.append(term.op().name());

            if (!declarations.containsKey(term.op().name().toString()) && !(term.op() instanceof QuantifiableVariable) &&
                !(term.equals(services.getTermBuilder().tt())) && !(term.equals(services.getTermBuilder().ff()))) {

                String sort = translateSort(term.sort());
                if (term.sort() instanceof ArraySort) {
                    sort = "(" + sort + ")";
                }

                declarations.put(term.op().name().toString(),
                        "(declare-fun " + term.op().name() + " () " + sort + ")\n");
            }
        }

        // Integer Comparison Operators
        else if (term.op().equals(integerLDT.getLessOrEquals())) {
            binaryTranslate(term.sub(0), term.sub(1), "<=", declarations, problemBuilder);
        } else if (term.op().equals(integerLDT.getGreaterOrEquals())) {
            binaryTranslate(term.sub(0), term.sub(1), ">=", declarations, problemBuilder);
        } else if (term.op().equals(integerLDT.getLessThan())) {
            binaryTranslate(term.sub(0), term.sub(1), "<", declarations, problemBuilder);
        } else if (term.op().equals(integerLDT.getGreaterThan())) {
            binaryTranslate(term.sub(0), term.sub(1), ">", declarations, problemBuilder);
        } else if (term.op().equals(Equality.EQUALS) || term.op().equals(Equality.EQV)) {
            binaryTranslate(term.sub(0), term.sub(1), "=", declarations, problemBuilder);
        }

        // Integer Arithmetic Operators
        else if (term.op().equals(integerLDT.getAdd())) {
            binaryTranslate(term.sub(0), term.sub(1), "+", declarations, problemBuilder);
        } else if (term.op().equals(integerLDT.getSub())) {
            binaryTranslate(term.sub(0), term.sub(1), "-", declarations, problemBuilder);
        } else if (term.op().equals(integerLDT.getMul())) {
            binaryTranslate(term.sub(0), term.sub(1), "*", declarations, problemBuilder);
        } else if (term.op().equals(integerLDT.getJDivision())) {
            binaryTranslate(term.sub(0), term.sub(1), "div", declarations, problemBuilder);
        }

        // Logical Operators
        else if (term.op().equals(Junctor.AND)) {
            binaryTranslate(term.sub(0), term.sub(1), "and", declarations, problemBuilder);
        } else if (term.op().equals(Junctor.OR)) {
            binaryTranslate(term.sub(0), term.sub(1), "or", declarations, problemBuilder);
        } else if (term.op().equals(Junctor.NOT)) {
            unaryTranslate(term.sub(0), "not", declarations, problemBuilder);
        } else if (term.op().equals(Junctor.IMP)) {
            binaryTranslate(term.sub(0), term.sub(1), "=>", declarations, problemBuilder);
        }

        // Quantifiers
        else if (term.op().equals(Quantifier.ALL)) {
            QuantifiableVariable boundVar = term.boundVars().get(0);
            problemBuilder.append("(forall ((").append(boundVar.name()).append(" ").append(translateSort(boundVar.sort())).append(")) ");
            recursiveTranslate(term.sub(0), declarations, problemBuilder);
            problemBuilder.append(")");
        }

        else if (term.op().equals(Quantifier.EX)) {
            QuantifiableVariable boundVar = term.boundVars().get(0);
            problemBuilder.append("(forall ((").append(boundVar.name()).append(" ").append(translateSort(boundVar.sort())).append(")) ");
            recursiveTranslate(term.sub(0), declarations, problemBuilder);
            problemBuilder.append(")");
        }

        else if (term.op().name().toString().equals(LENGTH_FUNCTION)) {
            unaryTranslate(term.sub(0), LENGTH_FUNCTION, declarations, problemBuilder);
        }

        else if (term.op().name().toString().equals(ARR_FUNCTION)) {
            recursiveTranslate(term.sub(0), declarations, problemBuilder);
        }

        else if (term.op() instanceof SortDependingFunction sdf) {
            String functionName = sdf.getKind().toString();
            if (functionName.equals("select")) {
                binaryTranslate(term.sub(1), term.sub(2), "select", declarations, problemBuilder);
            } else {
                throw new IllegalArgumentException("Unsupported operator: " + term);
            }
        }

        // Uninterpreted Functions
        else if (term.op().sort(new Sort[] {}).equals(JavaDLTheory.FORMULA)) {
            StringBuilder functionBuilder = new StringBuilder();
            functionBuilder.append("(declare-fun ").append(term.op().name()).append(" ( ");
            term.subs().forEach(sub -> functionBuilder.append(translateSort(sub.sort())).append(" "));
            functionBuilder.append(") Bool)\n");
            declarations.put(term.op().name().toString(), functionBuilder.toString());

            problemBuilder.append("(").append(term.op().name()).append(" ");
            for (int i = 0; i < term.subs().size(); i++) {
                recursiveTranslate(term.sub(i), declarations, problemBuilder);
                if (i != term.subs().size() - 1) {
                    problemBuilder.append(" ");
                }
            }
            problemBuilder.append(")");
        }

        // Constants
        else if (term.op().toString().equals("Z")) {
            // Should be evaluated to the number behind the Z term
            if (term.sub(0).op().name().toString().equals("neglit")) {
                problemBuilder.append("-").append(term.sub(0).sub(0).op().name());
            } else {
                problemBuilder.append(term.sub(0).op().name());
            }
        }

        else {
            throw new IllegalArgumentException("Unsupported operator: " + term);
        }
    }

    private void unaryTranslate(Term term, String functionSymbol, Map<String, String> declarations, StringBuilder problemBuilder) {
        problemBuilder.append("(").append(functionSymbol).append(" ");
        recursiveTranslate(term, declarations, problemBuilder);
        problemBuilder.append(")");
    }

    private void binaryTranslate(Term termLeft, Term termRight, String functionSymbol, Map<String, String> declarations, StringBuilder problemBuilder) {
        problemBuilder.append("(").append(functionSymbol).append(" ");
        recursiveTranslate(termLeft, declarations, problemBuilder);
        problemBuilder.append(" ");
        recursiveTranslate(termRight, declarations, problemBuilder);
        problemBuilder.append(")");
    }

    private String translateSort(Sort sort) {
        if (sort.equals(integerLDT.targetSort())) {
            return "Int";
        }

        else if (sort instanceof ArraySort arraySort) {
            return "Array Int " + translateSort(arraySort.elementSort());
        }

        else {
            throw new IllegalArgumentException("Unsupported sort: " + sort);
        }
    }

}
