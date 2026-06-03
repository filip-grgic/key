package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure.VariableBounds;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.engine.ProofSearchInformation;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import java.util.*;

public class VerificationCondition {

    private final Sequent sequent;
    private final Services services;
    private final ProofEnvironment proofEnv;
    private Term quantifiedInvariant;
    private final Term function;
    private final Map<Name, LogicVariable> quantVars;

    private final VCKind vckind;

    private final Map<Tuple<Term, Term>, Operator> antecedentRelations;

    private final Map<Tuple<Term, Term>, Operator> succedentRelations;

    private final List<Term> antecedentTerms;

    private final List<Term> succedentTerms;


    public VerificationCondition(Services services, Sequent sequent, LoopSpecification loopSpecification) {
        this.services = services;
        this.proofEnv = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
//        this.sequent = prepareSequent(sequent);
        this.sequent = sequent;
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
        antecedentTerms = collectRelevantTerms(this.sequent.antecedent());
        succedentTerms = collectRelevantTerms(this.sequent.succedent());
//        this.sequent.antecedent().forEach(sf -> antecedentTerms.add(sf.formula()));
//        this.sequent.succedent().forEach(sf -> succedentTerms.add(sf.formula()));

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
        return antecedentRelations.keySet().stream().toList();
    }

    public List<Tuple<Term, Term>> getSuccedentRelations() {
        return succedentRelations.keySet().stream().toList();
    }

    public Map<Tuple<Term, Term>, Operator> getAntecedentRelationOperators() {
        return antecedentRelations;
    }

    public Map<Tuple<Term, Term>, Operator> getSuccedentRelationOperators() {
        return succedentRelations;
    }

    public List<Term> getAntecedentTerms() {
        return antecedentTerms;
    }

    public List<Term> getSuccedentTerms() {
        return succedentTerms;
    }

    public VariableBounds getBounds(Term term) {
//        Set<Term> lowerBounds = new HashSet<>();
//        Set<Term> upperBounds = new HashSet<>();
        VariableBounds result = new VariableBounds(services);
        IntegerLDT integerLDT = services.getTypeConverter().getIntegerLDT();
        for (Tuple<Term, Term> relation : antecedentRelations.keySet()) {
            if (relation.first().equals(term)) {
                if (antecedentRelations.get(relation).equals(integerLDT.getGreaterOrEquals())) {
                    result.addLowerBound(relation.second());
//                    lowerBounds.add(relation.second());
                } else if (antecedentRelations.get(relation).equals(integerLDT.getLessOrEquals())) {
                    result.addUpperBound(relation.second());
//                    upperBounds.add(relation.second());
                }
            } else if (relation.second().equals(term)) {
                if (antecedentRelations.get(relation).equals(integerLDT.getGreaterOrEquals())) {
                    result.addUpperBound(relation.first());
//                    upperBounds.add(relation.first());
                } else if (antecedentRelations.get(relation).equals(integerLDT.getLessOrEquals())) {
                    result.addLowerBound(relation.first());
//                    lowerBounds.add(relation.first());
                }
            }
        }
        return result;
    }

    private Map<Tuple<Term, Term>, Operator> collectBinaryRelations(Semisequent semisequent) {
        Map<Tuple<Term, Term>, Operator> result = new HashMap<>();

        for (SequentFormula sequentFormula : semisequent.asList()) {
            if (formulaContainsForbidden(sequentFormula.formula())) {
                continue;
            }
            FreeBinaryTermCollector btc = new FreeBinaryTermCollector();
            sequentFormula.formula().execPostOrder(btc);
            result.putAll(btc.result());
        }

        return result;
    }

    private List<Term> collectRelevantTerms(Semisequent semisequent) {
        List<Term> result = new ArrayList<>();
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        for (SequentFormula sequentFormula : semisequent.asList()) {
            Term formula = sequentFormula.formula();
            if (formula.op().equals(heapLDT.getWellFormed())) {
                continue;
            } else if (formula.op().equals(this.function.op())) {
                continue;
            } else if (formulaContainsForbidden(formula)) {
                continue;
            } else if (formula.toString().contains("anon")) {
                formula = removeAnonymisation(formula, heapLDT);
            }
            result.add(formula);
        }
        return result;
    }

    private Term removeAnonymisation(Term formula, HeapLDT heapLDT) {
        if (formula.op().equals(heapLDT.getAnon())) {
            return removeAnonymisation(formula.sub(0), heapLDT);
        } else if (!formula.subs().isEmpty()) {
            JTerm[] newSubs = new JTerm[formula.subs().size()];
            for (int i = 0; i < formula.subs().size(); i++) {
                newSubs[i] = (JTerm) removeAnonymisation(formula.sub(i), heapLDT);
            }

            if (formula.op() instanceof Quantifier) {
                ImmutableArray<QuantifiableVariable> quantVars = new ImmutableArray<>(formula.boundVars().stream().map(v -> (QuantifiableVariable) v).toList());
                return services.getTermFactory().createTerm(formula.op(), newSubs, quantVars, null);
            }
            return services.getTermFactory().createTerm(formula.op(), newSubs);
        }
        return formula;
    }

    public SMTResult checkFulfillment(Term term) {
//        Term preparedCandidate = createQuantification(term);
//        Sequent resultingSequent = sequent.addFormula(new SequentFormula(preparedCandidate), true, true)
//                .sequent();

        Sequent resultingSequent = insertCandidateIntoSequent(term);

        //Use KeY for checking validity of the resulting sequent
//        try {
//            ProofStarter starter = createProofStarter(resultingSequent);
//            ProofSearchInformation<Proof, Goal> pi = starter.start();
//            if (pi.getProof().openGoals().isEmpty()) {
//                return new SMTResult(true);
//            }
//        } catch (ProofInputException ex) {
//            return new SMTResult(false);
//        }

        //SMT Solver for counterexample generation
        SMTInstance smtInstance = new SMTInstance(resultingSequent, services);
        smtInstance.processSMTProblem();
        return smtInstance.result();
    }

    private ProofStarter createProofStarter(Sequent sequent) throws ProofInputException {
        ProofStarter starter = new ProofStarter(false);
        starter.init(sequent, proofEnv, "VC proof");

        Proof proof = starter.getProof();
        assert proof != null;

        FunctionalOperationContractPO po = new FunctionalOperationContractPO(proof.getInitConfig(), (FunctionalOperationContract) services.getSpecificationRepository().getContractPOForProof(services.getProof()).getContract());
        po.registerClassAxiomTaclets(po.getContainerType(), proof.getInitConfig());
        proof.getOpenGoal(proof.root()).indexOfTaclets().addTaclets(
                po.getInitialTaclets()
        );

        return starter;
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
//        } else if (term.sort().equals(services.getTypeConverter().getHeapLDT().targetSort())) {
//            return true;
        } else if (term.op().name().toString().equals("self")) {
            return true;
        } else if (term.sort().name().toString().equals("Field") && !term.op().name().toString().equals("arr")) {
            return true;
        } else if (term.sort().name().toString().equals("java.lang.Object")) {
            return true;
        } else if (term.op() instanceof Equality &&
                (term.sub(0).sort() instanceof NullSort || term.sub(1).sort() instanceof NullSort)) {
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

    public List<Tuple<Term, Term>> getInitUpdates() {
        List<Tuple<Term, Term>> result = new ArrayList<>();
        if (!vckind.equals(VCKind.INITIATION)) {
            return result;
        }

        Term updatedFunction = null;

        for (Term term : sequent.succedent().asList().stream().map(SequentFormula::formula).toList()) {
            if (term.op().equals(function.op())) {
                updatedFunction = term;
                break;
            }
        }

        if (updatedFunction == null) {
            return result;
        }

        for (int i = 0; i < updatedFunction.subs().size(); i++) {
            if (!updatedFunction.sub(i).equals(function.sub(i)) &&
                    !function.sub(i).toString().equals("_" + updatedFunction.sub(i)) &&
                    function.sub(i).sort().equals(services.getTypeConverter().getIntegerLDT().targetSort())) {
                result.add(new Tuple<>(updatedFunction.sub(i), function.sub(i)));
            }
        }

        return result;
    }

    public enum VCKind {
        INITIATION, CONSECUTION, COMPLETION, EXTERNAL
    }

}
