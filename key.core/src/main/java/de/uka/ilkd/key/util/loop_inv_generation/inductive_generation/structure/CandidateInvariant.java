package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Tuple;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.util.collection.Pair;

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
                result = services.getTermBuilder().and((JTerm) result, (JTerm) vcSourcedConjuncts.get(key).translateToTerm());
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
        System.out.println(getHistoryString());
    }

    private String getHistoryString() {
        StringBuilder result = new StringBuilder();
        for (CandidateInvariant candidateInvariant : history) {
            result.append(candidateInvariant);
            result.append(", ");
        }
        return result.toString();
    }

    public int getHistorySize() {
        return history.size();
    }

    public Set<Tuple<Term, Term>> getRelationSources() {
        return relationSourcedConjuncts.keySet();
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

    public VariableBounds getBounds(Term term) {
//        Set<Term> lowerBounds = new HashSet<>();
//        Set<Term> upperBounds = new HashSet<>();
        VariableBounds result = new VariableBounds(services);
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        for (Tuple<Term, Term> relation : relationSourcedConjuncts.keySet()) {
            if (relation.first().equals(term) || relation.second().equals(term)) {
                Term first = relationSourcedConjuncts.get(relation).sub(0);
                Term second = relationSourcedConjuncts.get(relation).sub(1);

                if (first.equals(term)) {
                    if (relationSourcedConjuncts.get(relation).op().equals(integerLDT.getGreaterOrEquals())) {
                        result.addLowerBound(second);
                    } else if (relationSourcedConjuncts.get(relation).op().equals(integerLDT.getLessOrEquals())) {
                        result.addUpperBound(second);
                        //upperBounds.add(second);
                    }
                } else if (second.equals(term)) {
                    if (relationSourcedConjuncts.get(relation).op().equals(integerLDT.getGreaterOrEquals())) {
                        result.addUpperBound(first);
//                        upperBounds.add(first);
                    } else if (relationSourcedConjuncts.get(relation).op().equals(integerLDT.getLessOrEquals())) {
                        result.addLowerBound(first);
//                        lowerBounds.add(first);
                    }
                }
            }
        }
        return result;
    }

    public Set<Tuple<Term, Term>> collectEqualities(List<Term> antecedentTerms) {
        Set<Tuple<Term, Term>> result = new HashSet<>();
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();

        List<Term> allTerms = new ArrayList<>(conjuncts());
        allTerms.addAll(antecedentTerms);
        List<Pair<Operator, Tuple<Term,Term>>> termsWithOps = allTerms.stream()
                .filter(t -> t.subs().size() == 2)
                .map(t -> new Pair<>(t.op(), new Tuple<>(t.sub(0), t.sub(1))))
                .toList();

        for (int i = 0; i < termsWithOps.size(); i++) {
            Pair<Operator, Tuple<Term,Term>> pair = termsWithOps.get(i);
            Operator op = pair.first;
            Tuple<Term,Term> tuple = pair.second;
            if (op instanceof Equality) {
                result.add(tuple);
                continue;
            }

            if (op.equals(integerLDT.getGreaterOrEquals())) {
                for (int j = i+1; j < termsWithOps.size(); j++) {
                    if (!tuple.equals(termsWithOps.get(j).second)) {
                        continue;
                    }
                    Pair<Operator, Tuple<Term,Term>> otherPair = termsWithOps.get(j);
                    if ((otherPair.first.equals(integerLDT.getLessOrEquals()) &&
                            tuple.first().equals(otherPair.second.first())) ||
                            otherPair.first.equals(integerLDT.getGreaterOrEquals())) {
                        result.add(tuple);
                    }
                }
            }

            else if (op.equals(integerLDT.getLessOrEquals())) {
                for (int j = i+1; j < termsWithOps.size(); j++) {
                    if (!tuple.equals(termsWithOps.get(j).second)) {
                        continue;
                    }
                    Pair<Operator, Tuple<Term,Term>> otherPair = termsWithOps.get(j);
                    if ((otherPair.first.equals(integerLDT.getGreaterOrEquals()) &&
                        tuple.first().equals(otherPair.second.first())) ||
                        otherPair.first.equals(integerLDT.getLessOrEquals())) {
                        result.add(tuple);
                    }
                }
            }
        }

        return result;
    }
}
