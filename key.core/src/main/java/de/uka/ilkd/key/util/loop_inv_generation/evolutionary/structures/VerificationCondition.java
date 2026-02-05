package de.uka.ilkd.key.util.loop_inv_generation.evolutionary.structures;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSettings;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
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

    private final SolverType smtSolver;

    public VerificationCondition(Services services, Sequent sequent, LoopSpecification loopSpecification, SolverType smtSolver) {
        this.services = services;
//        this.sequent = prepareSequent(sequent);
        this.sequent = sequent;
        this.function = loopSpecification.getInvariant(services);
        this.smtSolver = smtSolver;
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

    }

    public boolean checkFulfillment(LoopInvariantFreeGenome genome) {
        Term preparedCandidate = createQuantification(genome);

        //We want to ignore invariant candidates that are trivially true or false (e.g. by containing contradicting terms)
        //or that contain the variable representing the method's return value, as the invariant cannot contain it
        if (checkForReturnValue(genome) || checkForTriviality(genome.translateToTerm())) {
            return false;
        }

        Sequent resultingSequent = sequent.addFormula(new SequentFormula(preparedCandidate), true, true)
                .sequent();

//        ImmutableList<SequentFormula> insertedAntecedent = insertInvariant(genome.translateToTerm(), sequent.antecedent());
//        ImmutableList<SequentFormula> insertedSuccedent = insertInvariant(genome.translateToTerm(), sequent.succedent());
//
//        Sequent resultingSequent = JavaDLSequentKit.createSequent(insertedAntecedent, insertedSuccedent);

        SMTProblem smtProblem = new SMTProblem(resultingSequent, services);

        SolverLauncher launcher = getSolverLauncher();
        launcher.launch(smtProblem, services, smtSolver);

        return smtProblem.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID;
    }

    private Sequent prepareSequent(Sequent sequent) {
        ImmutableList<SequentFormula> newAntecedent = removeForbiddenFromSemiSequent(sequent.antecedent());
        ImmutableList<SequentFormula> newSuccedent = removeForbiddenFromSemiSequent(sequent.succedent());

        return JavaDLSequentKit.createSequent(newAntecedent, newSuccedent);
    }

    private ImmutableList<SequentFormula> removeForbiddenFromSemiSequent(Semisequent semisequent) {
        List<SequentFormula> newSemisequent = new ArrayList<>();

        for (SequentFormula sequentFormula : semisequent.asList()) {
            if (formulaContainsForbidden(sequentFormula.formula())) {
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
        } else if (term.sort().name().toString().equals("Field")) {
            return true;
        } else if (term.sort().name().toString().equals("java.lang.Object")) {
            return true;
        }

        for (Term sub : term.subs()) {
            if (formulaContainsForbidden(sub)) {
                return true;
            }
        }

        return false;
    }

    private ImmutableList<SequentFormula> insertInvariant(Term candidate, Semisequent semisequent) {
        List<SequentFormula> insertedSemisequent = new ArrayList<>();
        TermBuilder termBuilder = services.getTermBuilder();

        for (SequentFormula sequentFormula : semisequent.asList()) {
            if (!sequentFormula.formula().op().name().toString().equals(function.op().name().toString())) {
                insertedSemisequent.add(sequentFormula);
                continue;
            }

            Term freshInv = sequentFormula.formula();
            Term resultingSequentFormula = candidate;

            for (int i = 0; i < freshInv.subs().size(); i++) {
                resultingSequentFormula = termBuilder.replaceContainingTerm(resultingSequentFormula, function.sub(i), freshInv.sub(i));
            }

            insertedSemisequent.add(new SequentFormula(resultingSequentFormula));

        }

        return ImmutableList.of(insertedSemisequent.toArray(new SequentFormula[0]));
    }

    private boolean checkForTriviality(Term preparedCandidate) {
        SolverLauncher launcher = getSolverLauncher();
        TermBuilder termBuilder = services.getTermBuilder();
//        ImmutableList<SequentFormula> trueAnte = ImmutableList.of(new SequentFormula(termBuilder.tt()));

        ImmutableList<SequentFormula> trueTrivialSucc = ImmutableList.of(new SequentFormula(preparedCandidate));
        Sequent sequent = JavaDLSequentKit.createAnteSequent(trueTrivialSucc);

        SMTProblem checkForTrue = new SMTProblem(sequent, services);
        launcher.launch(checkForTrue, services, smtSolver);
        boolean triviallyTrue = checkForTrue.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID;

        return triviallyTrue;

//        if (triviallyTrue) {
//            return true;
//        }
//
//        launcher = getSolverLauncher();
//
//        ImmutableList<SequentFormula> falseTrivialSucc = ImmutableList.of(new SequentFormula(termBuilder.not((JTerm) preparedCandidate)));
//        sequent = JavaDLSequentKit.createSequent(trueAnte, falseTrivialSucc);
//
//        SMTProblem checkForFalse = new SMTProblem(sequent, services);
//        launcher.launch(checkForFalse, services, SMTSolver);
//
//        return checkForFalse.getFinalResult().isValid() == SMTSolverResult.ThreeValuedTruth.VALID;
    }

    private boolean checkForReturnValue(LoopInvariantFreeGenome genome) {
        for (Term term: genome.getContainingTerms()) {
            if (term.op().name().toString().startsWith("result_")) {
                return true;
            }
        }

        return false;
    }

    private SolverLauncher getSolverLauncher() {
        ProofIndependentSMTSettings piSettings = ProofIndependentSMTSettings.getDefaultSettingsData();
        piSettings.setStoreSMTTranslationToFile(true);
        piSettings.setShowResultsAfterExecution(true);
        piSettings.setPathForSMTTranslation("/home/filip/smttranslations");

        SMTSettings smtSettings = new DefaultSMTSettings(
                services.getProof().getSettings().getSMTSettings(),
                piSettings,
                new NewSMTTranslationSettings(),
                services.getProof()
        );

        return new SolverLauncher(smtSettings);
    }

    private Term createQuantification(LoopInvariantFreeGenome genome) {
        TermBuilder termBuilder = services.getTermBuilder();
        Term invariantCandidate = genome.translateToTerm();

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

}
