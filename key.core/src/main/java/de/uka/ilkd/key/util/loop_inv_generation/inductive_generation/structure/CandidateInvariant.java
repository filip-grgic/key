package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Tuple;
import org.key_project.logic.Term;

import java.util.*;

public class CandidateInvariant {

    private final Map<Term,Conjunct> vcSourcedConjuncts;
    private final Map<Tuple<Term,Term>,Term> relationSourcedConjuncts;
    private final Services services;
    private List<CandidateInvariant> history;

    public CandidateInvariant(Services services) {
        this(new HashMap<>(), new HashMap<>(), services);
    }

    public CandidateInvariant(Map<Term,Conjunct> vcSourcedConjuncts, Map<Tuple<Term,Term>,Term> relationSourcedConjuncts, Services services) {
        this.vcSourcedConjuncts = vcSourcedConjuncts;
        this.relationSourcedConjuncts = relationSourcedConjuncts;
        this.services = services;
        this.history = new ArrayList<>();
    }

    public CandidateInvariant(CandidateInvariant candidateInvariant) {
        this(new HashMap<>(candidateInvariant.vcSourcedConjuncts), new HashMap<>(candidateInvariant.relationSourcedConjuncts), candidateInvariant.services);
        this.history = new ArrayList<>(candidateInvariant.history);
        this.history.add(candidateInvariant);
    }

    public Term translateToTerm() {
        if (isEmpty()) {
            return services.getTermBuilder().tt();
        }

        Term result = null;

        for (Term key : vcSourcedConjuncts.keySet()) {
            if (result == null) {
                result = vcSourcedConjuncts.get(key).translateToTerm();
            } else {
                result = services.getTermBuilder().and((JTerm) result, (JTerm) vcSourcedConjuncts.get(key));
            }
        }

        for (Tuple<Term, Term> key : relationSourcedConjuncts.keySet()) {
            if (result == null) {
                result = relationSourcedConjuncts.get(key);
            } else {
                result = services.getTermBuilder().and((JTerm) result, (JTerm) relationSourcedConjuncts.get(key));
            }
        }

        return result;
    }

    public void addConjunct(Term source, Conjunct conjunct) {
        vcSourcedConjuncts.put(source, conjunct);
    }

    public void addConjunct(Tuple<Term, Term> source, Term conjunct) {
        relationSourcedConjuncts.put(source, conjunct);
    }

    public boolean containsSource(Term source) {
        return vcSourcedConjuncts.containsKey(source);
    }

    public boolean containsSource(Tuple<Term, Term> source) {
        return relationSourcedConjuncts.containsKey(source);
    }

    public boolean isEmpty() {
        return vcSourcedConjuncts.isEmpty() && relationSourcedConjuncts.isEmpty();
    }

    public boolean repeatingHistory() {
        return history.contains(this);
    }

    public void printHistory() {
        System.out.print("History: ");
        for (CandidateInvariant candidateInvariant : history) {
            System.out.print(candidateInvariant);
            System.out.print(", ");
        }
        System.out.println();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof CandidateInvariant that)) return false;
        if (vcSourcedConjuncts.size() != that.vcSourcedConjuncts.size()) return false;
        if (relationSourcedConjuncts.size() != that.relationSourcedConjuncts.size()) return false;

        for (Term key : vcSourcedConjuncts.keySet()) {
            if (!that.containsSource(key)) {
                return false;
            }
            if (!vcSourcedConjuncts.get(key).equals(that.vcSourcedConjuncts.get(key))) {
                return false;
            }
        }

        for (Tuple<Term,Term> key : relationSourcedConjuncts.keySet()) {
            if (!that.containsSource(key)) {
                return false;
            }
            if (!relationSourcedConjuncts.get(key).equals(that.relationSourcedConjuncts.get(key))) {
                return false;
            }
        }

        return true;
    }

    @Override
    public int hashCode() {
        int hash = 7;
        hash = 37 * hash + vcSourcedConjuncts.hashCode();
        hash = 37 * hash + relationSourcedConjuncts.hashCode();
        return hash;
    }

    public void replaceTerm(Term oldTerm, Term newTerm) {
        vcSourcedConjuncts.replaceAll((k, v) -> vcSourcedConjuncts.get(k).replace(oldTerm, newTerm));
        relationSourcedConjuncts.replaceAll((k, v) -> services.getTermBuilder().replaceContainingTerm(relationSourcedConjuncts.get(k), oldTerm, newTerm));
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        result.append("|");
        for (Term key : vcSourcedConjuncts.keySet()) {
            result.append(vcSourcedConjuncts.get(key)).append("|");
        }
        for (Tuple<Term,Term> key : relationSourcedConjuncts.keySet()) {
            result.append(relationSourcedConjuncts.get(key)).append("|");
        }
        return result.toString();
    }

    private List<Term> conjuncts() {
        List<Term> result = new ArrayList<>();
        result.addAll(vcSourcedConjuncts.values().stream().map(Conjunct::translateToTerm).toList());
        result.addAll(relationSourcedConjuncts.values());
        return result;
    }

    public Set<Tuple<Term, Term>> collectEqualities(List<Term> antecedentTerms) {
        Set<Tuple<Term, Term>> result = new HashSet<>();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        List<Term> allTerms = new ArrayList<>(conjuncts());
        allTerms.addAll(antecedentTerms);

        for (int i = 0; i < allTerms.size(); i++) {
            Term term = allTerms.get(i);
            if (term.op() instanceof Equality) {
                result.add(new Tuple<>(term.sub(0), term.sub(1)));
            }

            else if (term.op().equals(integerLDT.getGreaterOrEquals())) {
                for (int j = i+1; j < allTerms.size(); j++) {
                    Term otherTerm = allTerms.get(j);
                    if (otherTerm.op().equals(integerLDT.getLessOrEquals())) {
                        result.add(new Tuple<>(term.sub(0), term.sub(1)));
                    }
                }
            }

            else if (term.op().equals(integerLDT.getLessOrEquals())) {
                for (int j = i+1; j < allTerms.size(); j++) {
                    Term otherTerm = allTerms.get(j);
                    if (otherTerm.op().equals(integerLDT.getGreaterOrEquals())) {
                        result.add(new Tuple<>(term.sub(0), term.sub(1)));
                    }
                }
            }
        }

        return result;
    }
}
