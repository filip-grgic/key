package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.speclang.LoopSpecification;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.Pair;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class VerificationCondition {

    private final Sequent sequent;
    private final Services services;
    private Term quantifiedInvariant;
    private final Term function;
    private final Map<Name, LogicVariable> quantVars;

    private final VCKind vckind;

    private List<Tuple<Term,Term>> antecedentRelations;

    private List<Tuple<Term,Term>> succedentRelations;

    private List<Term> antecedentTerms = new ArrayList<>();

    private List<Term> succedentTerms = new ArrayList<>();


    public VerificationCondition(Services services, Sequent sequent, LoopSpecification loopSpecification) {
        this.services = services;
        this.sequent = prepareSequent(sequent);
//        this.sequent = sequent;
        this.function = loopSpecification.getInvariant(services);
        TermBuilder termBuilder = services.getTermBuilder();

        if (!(function.op() instanceof Function)) {
            throw new IllegalArgumentException("The invariant in the specified loop specification is not a function");
        }

        TermFactory termFactory = services.getTermFactory();

        quantVars = new HashMap<>();
        quantifiedInvariant = termFactory.createTerm((JTerm) function);

        for (Term par : function.subs()) {
            Name newName = new Name(termBuilder.newName(par.op().name().toString()));
            LogicVariable quantVar = new LogicVariable(newName, par.op().sort(new Sort[0]));
            quantVars.put(par.op().name(), quantVar);
            quantifiedInvariant = termBuilder.replaceVariable(quantifiedInvariant, par.op().name(), quantVar);
        }

        boolean invInAnte = this.sequent.antecedent().toString().contains(function.op().name().toString());
        boolean invInSucc = this.sequent.succedent().toString().contains(function.op().name().toString());

        antecedentRelations = collectBinaryRelations(this.sequent.antecedent());
        succedentRelations = collectBinaryRelations(this.sequent.succedent());

        this.sequent.antecedent().forEach(sf -> antecedentTerms.add(sf.formula()));
        this.sequent.succedent().forEach(sf -> succedentTerms.add(sf.formula()));

        if (invInAnte && invInSucc) {
            vckind = VCKind.CONSECUTION;
        } else if (invInAnte) {
            vckind = VCKind.COMPLETION;
        } else if (invInSucc) {
            vckind = VCKind.INITIATION;
        } else {
            vckind = VCKind.EXTERNAL;
        }

    }

    public List<Tuple<Term, Term>> getAntecedentRelations() {
        return antecedentRelations;
    }

    public List<Tuple<Term, Term>> getSuccedentRelations() {
        return succedentRelations;
    }

    public List<Term> getAntecedentTerms() {
        return antecedentTerms;
    }

    public List<Term> getSuccedentTerms() {
        return succedentTerms;
    }

    private List<Tuple<Term,Term>> collectBinaryRelations(Semisequent semisequent) {
        List<Tuple<Term,Term>> result = new ArrayList<>();

        for (SequentFormula sequentFormula : semisequent.asList()) {
            BinaryTermCollector btc = new BinaryTermCollector();
            sequentFormula.formula().execPostOrder(btc);
            result.addAll(btc.result());
        }

        return result;
    }

    public SMTResult checkFulfillment(Term term) {
//        Term preparedCandidate = createQuantification(term);
//        Sequent resultingSequent = sequent.addFormula(new SequentFormula(preparedCandidate), true, true)
//                .sequent();
        Sequent resultingSequent = insertCandidateIntoSequent(term);

        SMTInstance smtInstance = new SMTInstance(resultingSequent, services);
        smtInstance.processSMTProblem();
        return smtInstance.result();
    }

    private Sequent prepareSequent(Sequent sequent) {
        ImmutableList<SequentFormula> newAntecedent = removeForbiddenFromSemiSequent(sequent.antecedent());
        ImmutableList<SequentFormula> newSuccedent = removeForbiddenFromSemiSequent(sequent.succedent());

        return JavaDLSequentKit.createSequent(newAntecedent, newSuccedent);
    }

    private ImmutableList<SequentFormula> removeForbiddenFromSemiSequent(Semisequent semisequent) {
        List<SequentFormula> newSemisequent = new ArrayList<>();
        List<SequentFormula> thrownOut = new ArrayList<>();

        for (SequentFormula sequentFormula : semisequent.asList()) {
            if (formulaContainsForbidden(sequentFormula.formula())) {
                thrownOut.add(sequentFormula);
                continue;
            }

            newSemisequent.add(sequentFormula);
        }

        return ImmutableList.of(newSemisequent.toArray(new SequentFormula[0]));
    }

    private boolean formulaContainsForbidden(Term term) {

        if (term.op().name().toString().equals("measuredByEmpty")) {
            return true;
        } else if (term.sort().equals(services.getTypeConverter().getHeapLDT().targetSort())) {
            return true;
        } else if (term.op().name().toString().equals("self")) {
            return true;
        } else if (term.sort().name().toString().equals("Field") && !term.op().name().toString().equals("arr")) {
            return true;
        } else if (term.sort().name().toString().equals("java.lang.Object")) {
            return true;
        }

        for (int i = 0; i < term.subs().size(); i++) {
            if (term.op().name().toString().endsWith("::select") && i == 0) {
                continue;
            }
            Term sub = term.sub(i);
            if (formulaContainsForbidden(sub)) {
                return true;
            }
        }

        return false;
    }

    private Sequent insertCandidateIntoSequent(Term invariantCandidate) {
        List<SequentFormula> newAntecedent = new ArrayList<>();
        List<SequentFormula> newSuccedent = new ArrayList<>();

        for (SequentFormula sequentFormula : sequent.antecedent().asList()) {
            newAntecedent.add(insertCandidateIntoFormula(invariantCandidate, sequentFormula));
        }

        for (SequentFormula sequentFormula : sequent.succedent().asList()) {
            newSuccedent.add(insertCandidateIntoFormula(invariantCandidate, sequentFormula));
        }

        return JavaDLSequentKit.createSequent(
                ImmutableList.of(newAntecedent.toArray(new SequentFormula[0])),
                ImmutableList.of(newSuccedent.toArray(new SequentFormula[0]))
        );
    }

    private SequentFormula insertCandidateIntoFormula(Term invariantCandidate, SequentFormula sequentFormula) {
        Term formula = sequentFormula.formula();

        if (!formula.op().name().equals(function.op().name())) {
            return sequentFormula;
        }

        TermBuilder termBuilder = services.getTermBuilder();
        Term insertedCandidate = invariantCandidate;

        for (int i = 0; i < formula.subs().size(); i++) {
            insertedCandidate = termBuilder.replaceContainingTerm(insertedCandidate, function.sub(i), formula.sub(i));
        }

        return new SequentFormula(insertedCandidate);
    }

    private Term createQuantification(Term invariantCandidate) {
        TermBuilder termBuilder = services.getTermBuilder();

        List<QuantifiableVariable> quantVarsForTerm = new ArrayList<>();

        for (Map.Entry<Name, LogicVariable> entry : quantVars.entrySet()) {
            LogicVariable variable = entry.getValue();
            Name name = entry.getKey();

            invariantCandidate = termBuilder.replaceVariable(invariantCandidate, name, variable);
            quantVarsForTerm.add(variable);
        }

        return termBuilder.all(quantVarsForTerm,
                termBuilder.equals((JTerm) quantifiedInvariant, (JTerm) invariantCandidate));

    }

    public Sequent getSequent() {
        return sequent;
    }

    public VCKind getVCKind() {
        return vckind;
    }

    public enum VCKind {
        INITIATION, CONSECUTION, COMPLETION, EXTERNAL
    }

}
