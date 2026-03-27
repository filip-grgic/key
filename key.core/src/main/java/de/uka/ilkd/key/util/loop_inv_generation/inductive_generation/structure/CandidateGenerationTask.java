package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.SMTResult;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Tuple;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.VerificationCondition;
import org.key_project.logic.Term;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

public class CandidateGenerationTask implements Runnable {

    private final Services services;
    private final CandidateInvariant candidateInvariant;
    private final List<VerificationCondition> verificationConditions;
    private final AtomicBoolean isFinished;
    private final AtomicReference<Term> loopInvariant;
    private final BlockingQueue<CandidateGenerationTask> taskQueue;
    private final Set<CandidateInvariant> traversedCandidates;

    public CandidateGenerationTask(Services services, AtomicBoolean isFinished, AtomicReference<Term> loopInvariant, BlockingQueue<CandidateGenerationTask> taskQueue, Set<CandidateInvariant> traversedCandidates, CandidateInvariant candidateInvariant, List<VerificationCondition> verificationConditions) {
        this.services = services;
        this.candidateInvariant = candidateInvariant;
        this.verificationConditions = verificationConditions;
        this.isFinished = isFinished;
        this.loopInvariant = loopInvariant;
        this.taskQueue = taskQueue;
        this.traversedCandidates = traversedCandidates;
    }

    @Override
    public void run() {
        try {
            if (candidateInvariant.repeatingHistory()) {
                return;
            }

            if (traversedCandidates.contains(candidateInvariant)) {
                return;
            } else {
                traversedCandidates.add(candidateInvariant);
            }

            candidateInvariant.printHistory();
            System.out.println("Handling: " + candidateInvariant);

            if (checkVerificationConditions()) {
                loopInvariant.set(candidateInvariant.translateToTerm());
                isFinished.set(true);
            }
        } catch (InterruptedException e) {
            this.notify();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private boolean checkVerificationConditions() throws InterruptedException {
        boolean checksAllVCs = true;

        for (VerificationCondition vc : verificationConditions) {
            SMTResult result = vc.checkFulfillment(candidateInvariant.translateToTerm());
            if (!result.isValid()) {
                checksAllVCs = false;
                if (vc.getVCKind() == VerificationCondition.VCKind.INITIATION) {
                    handleInitiationCounterexample(vc, result);
                } else if (vc.getVCKind() == VerificationCondition.VCKind.CONSECUTION) {
                    handleConsecutionCounterexample(vc, result);
                } else if (vc.getVCKind() == VerificationCondition.VCKind.COMPLETION) {
                    handleCompletionCounterexample(vc, result);
                }
            }
        }

        return checksAllVCs;
    }

    private void handleInitiationCounterexample(VerificationCondition vc, SMTResult result) throws InterruptedException {
        System.err.println("Failed Initiation");
        throw new InterruptedException();
//        insertRelatedTerms(vc.getAntecedentRelations(), result);
    }

    private void handleConsecutionCounterexample(VerificationCondition vc, SMTResult result) throws InterruptedException {
//        replaceRelatedTerms(vc);
        insertRelatedTerms(vc.getAntecedentRelations(), result);
        insertRelatedTerms(vc.getSuccedentRelations(), result);
    }

    private void handleCompletionCounterexample(VerificationCondition vc, SMTResult result) throws InterruptedException {
        for (Term succedentTerm : vc.getSuccedentTerms()) {
            if (candidateInvariant.containsSource(succedentTerm)) {
                continue;
            }

            Set<Tuple<Term,Term>> equalities = candidateInvariant.collectEqualities(vc.getAntecedentTerms());
            createInsertedTask(succedentTerm, succedentTerm);
            for (Tuple<Term,Term> equality : equalities) {
                Term replaced1 = services.getTermBuilder().replaceContainingTerm(succedentTerm, equality.first(), equality.second());
                Term replaced2 = services.getTermBuilder().replaceContainingTerm(succedentTerm, equality.second(), equality.first());
                createInsertedTask(succedentTerm, replaced1);
                createInsertedTask(succedentTerm, replaced2);
            }
        }

//        replaceRelatedTerms(vc);
        insertRelatedTerms(vc.getAntecedentRelations(), result);
        insertRelatedTerms(vc.getSuccedentRelations(), result);
    }

    private void replaceRelatedTerms(VerificationCondition vc) throws InterruptedException {
        if (candidateInvariant.isEmpty()) {
            return;
        }
        for (Tuple<Term, Term> antecedentRelation : vc.getAntecedentRelations()) {
            CandidateInvariant extendedCandidate1 = new CandidateInvariant(candidateInvariant);
            extendedCandidate1.replaceTerm(antecedentRelation.first(), antecedentRelation.second());
            createExtendedTask(extendedCandidate1);
            CandidateInvariant extendedCandidate2 = new CandidateInvariant(candidateInvariant);
            extendedCandidate2.replaceTerm(antecedentRelation.second(), antecedentRelation.first());
            createExtendedTask(extendedCandidate2);
        }
    }

    private void insertRelatedTerms(List<Tuple<Term, Term>> relations, SMTResult result) throws InterruptedException {
        for (Tuple<Term, Term> relation : relations) {

            if (candidateInvariant.containsSource(relation)) {
                continue;
            }

            Term first = relation.first();
            Term second = relation.second();
            String firstName = first.op().name().toString();
            String secondName = second.op().name().toString();

            Map<String, Integer> counterexample = result.getCounterexampleConstants();

            if (!counterexample.containsKey(firstName) || !counterexample.containsKey(secondName)) {
                insertNaively(relation, (JTerm) first, (JTerm) second);
            } else {
                insertGuidedCE(relation, counterexample, (JTerm) first, (JTerm) second);
            }
        }
    }

    private void insertNaively(Tuple<Term, Term> relation, JTerm first, JTerm second) throws InterruptedException {
        TermBuilder tb = services.getTermBuilder();

        createInsertedTask(relation, tb.equals(first, second));
        createInsertedTask(relation, tb.geq(first, second));
        createInsertedTask(relation, tb.leq(first, second));
        createInsertedTask(relation, tb.gt(first, second));
        createInsertedTask(relation, tb.lt(first, second));
    }

    private void insertGuidedCE(Tuple<Term, Term> relation, Map<String, Integer> counterexample, JTerm first, JTerm second) throws InterruptedException {
        String firstName = first.op().name().toString();
        String secondName = second.op().name().toString();

        int firstCEValue = counterexample.get(firstName);
        int secondCEValue = counterexample.get(secondName);

        TermBuilder tb = services.getTermBuilder();

        if (firstCEValue == secondCEValue) {
            createInsertedTask(relation, tb.equals(first, second));
            createInsertedTask(relation, tb.geq(first, second));
            createInsertedTask(relation, tb.leq(first, second));
        } else if (firstCEValue < secondCEValue) {
            createInsertedTask(relation, tb.leq(first, second));
            createInsertedTask(relation, tb.lt(first, second));
            createInsertedTask(relation, tb.not(tb.equals(first, second)));
        } else {
            createInsertedTask(relation, tb.geq(first, second));
            createInsertedTask(relation, tb.gt(first, second));
            createInsertedTask(relation, tb.not(tb.equals(first, second)));
        }
    }

    private void createInsertedTask(Tuple<Term, Term> source, JTerm tb) throws InterruptedException {
        CandidateInvariant extendedCandidate = new CandidateInvariant(candidateInvariant);
        extendedCandidate.addConjunct(source, tb);
        createExtendedTask(extendedCandidate);
    }

    private void createInsertedTask(Term source, Term tb) throws InterruptedException {
        CandidateInvariant extendedCandidate = new CandidateInvariant(candidateInvariant);
        extendedCandidate.addConjunct(source, Conjunct.create(tb, services));
        createExtendedTask(extendedCandidate);
    }

    private void createExtendedTask(CandidateInvariant extendedCandidate) throws InterruptedException {
        taskQueue.put(new CandidateGenerationTask(services, isFinished, loopInvariant, taskQueue, traversedCandidates, extendedCandidate, verificationConditions));
    }

    @Override
    public String toString() {
        return candidateInvariant.toString();
    }
}
