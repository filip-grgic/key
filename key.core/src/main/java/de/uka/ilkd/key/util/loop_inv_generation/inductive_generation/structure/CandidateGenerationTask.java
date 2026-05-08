package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.init.ProofInitServiceUtil;
import de.uka.ilkd.key.util.SideProofUtil;
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
    private final List<VerificationCondition> initiationVCs;
    private final List<VerificationCondition> consecComplVCs;
    private final Set<LocationVariable> changingVariables;
    private CandidateInvariant candidateInvariant;
    private final List<VerificationCondition> verificationConditions;
    private final AtomicBoolean isFinished;
    private final AtomicReference<Term> loopInvariant;
    private final BlockingQueue<CandidateInvariant> taskQueue;
    private final Set<CandidateInvariant> traversedCandidates;
    private final int id;
    private int addedInRun;

    public CandidateGenerationTask(Services services, AtomicBoolean isFinished, AtomicReference<Term> loopInvariant, BlockingQueue<CandidateInvariant> taskQueue, Set<CandidateInvariant> traversedCandidates, List<VerificationCondition> verificationConditions, Set<LocationVariable> changingVariables, int id) {
        this.services = services;
        this.verificationConditions = verificationConditions;
        this.initiationVCs = verificationConditions.stream().filter(vc -> vc.getVCKind() == VerificationCondition.VCKind.INITIATION).toList();
        this.consecComplVCs = verificationConditions.stream().filter(vc -> vc.getVCKind() == VerificationCondition.VCKind.COMPLETION || vc.getVCKind() == VerificationCondition.VCKind.CONSECUTION).toList();
        this.isFinished = isFinished;
        this.loopInvariant = loopInvariant;
        this.taskQueue = taskQueue;
        this.traversedCandidates = traversedCandidates;
        this.changingVariables = changingVariables;
        this.id = id;
        this.addedInRun = 0;
    }

    @Override
    public void run() {
        try {
            //
            int i = 0;

            while (!isFinished.get()) {
                addedInRun = 0;
                //Try ten times to receive new task end stop after
                i = 0;
                candidateInvariant = taskQueue.poll();
                while (candidateInvariant == null) {
                    if (i >= 10) {
                        return;
                    }
                    Thread.sleep(id * 200);
                    i++;
                    candidateInvariant = taskQueue.poll();
                }

//                if (candidateInvariant.repeatingHistory()) {
//                    continue;
//                }
//
//                if (traversedCandidates.contains(candidateInvariant)) {
//                    continue;
//                } else {
//                    traversedCandidates.add(candidateInvariant);
//                }

//                if (candidateInvariant.toString().contains("all{")) {
//                    candidateInvariant.printHistory();
//                    System.out.println("Handling: " + candidateInvariant);
//                }

                if (checkVerificationConditions()) {
                    loopInvariant.set(candidateInvariant.translateToTerm());
                    isFinished.set(true);
                }
            }
        } catch (InterruptedException e) {
            this.notify();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private boolean checkVerificationConditions() throws InterruptedException {

        for (VerificationCondition vc : initiationVCs) {
            SMTResult result = vc.checkFulfillment(candidateInvariant.translateToTerm());
            if (!result.isValid()) {
                handleInitiationCounterexample(vc, result);
                return false;
            }
        }

        boolean checksAllVCs = true;

        for (VerificationCondition vc : consecComplVCs) {
            SMTResult result = vc.checkFulfillment(candidateInvariant.translateToTerm());
            if (!result.isValid()) {
                checksAllVCs = false;
                if (vc.getVCKind() == VerificationCondition.VCKind.CONSECUTION) {
                    handleConsecutionCounterexample(vc, result);
                } else if (vc.getVCKind() == VerificationCondition.VCKind.COMPLETION) {
                    handleCompletionCounterexample(vc, result);
                }
            }
        }

        return checksAllVCs;
    }

    private void handleInitiationCounterexample(VerificationCondition vc, SMTResult result) throws InterruptedException {
//        System.err.println("Failed Initiation");
//        insertRelatedTerms(vc.getAntecedentRelations(), result);
    }

    private void handleConsecutionCounterexample(VerificationCondition vc, SMTResult result) throws InterruptedException {
//        replaceRelatedTerms(vc);
        insertRelatedTerms(vc.getAntecedentRelations(), result, true);
        insertRelatedTerms(vc.getSuccedentRelations(), result, false);
    }

    private void handleCompletionCounterexample(VerificationCondition vc, SMTResult result) throws InterruptedException {
        for (Term succedentTerm : vc.getSuccedentTerms()) {
            if (candidateInvariant.containsSource(succedentTerm)) {
                continue;
            }
            createInsertedTask(succedentTerm, succedentTerm);

            if (succedentTerm.op().equals(Quantifier.ALL) || succedentTerm.op().equals(Quantifier.EX)) {
                BoundConjunct conjunct = (BoundConjunct) Conjunct.create(succedentTerm, services);
                Set<Term> boundedTerms = conjunct.getBoundedTerms();
                new BoundConjunct(conjunct);
            }
            handleEqualities(vc, succedentTerm);
        }

//        replaceRelatedTerms(vc);
        insertRelatedTerms(vc.getAntecedentRelations(), result, true);
        insertRelatedTerms(vc.getSuccedentRelations(), result, false);
    }

    private void handleEqualities(VerificationCondition vc, Term succedentTerm) throws InterruptedException {
        Set<Tuple<Term, Term>> equalities = candidateInvariant.collectEqualities(vc.getAntecedentTerms());
        for (Tuple<Term, Term> equality : equalities) {
            Term replaced1 = services.getTermBuilder().replaceContainingTerm(succedentTerm, equality.first(), equality.second());
            Term replaced2 = services.getTermBuilder().replaceContainingTerm(succedentTerm, equality.second(), equality.first());
            createInsertedTask(succedentTerm, replaced1);
            createInsertedTask(succedentTerm, replaced2);
        }
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

    private void insertRelatedTerms(List<Tuple<Term, Term>> relations, SMTResult result, boolean inAnte) throws InterruptedException {
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
            } else if (inAnte) {
                insertGuidedCE(relation, counterexample, (JTerm) first, (JTerm) second);
            } else {
                insertGuidedInverseCE(relation, counterexample, (JTerm) first, (JTerm) second);
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

    private void insertGuidedInverseCE(Tuple<Term, Term> relation, Map<String, Integer> counterexample, JTerm first, JTerm second) throws InterruptedException {
        String firstName = first.op().name().toString();
        String secondName = second.op().name().toString();

        int firstCEValue = counterexample.get(firstName);
        int secondCEValue = counterexample.get(secondName);

        TermBuilder tb = services.getTermBuilder();

        if (firstCEValue == secondCEValue) {
            createInsertedTask(relation, tb.not(tb.equals(first, second)));
            createInsertedTask(relation, tb.lt(first, second));
            createInsertedTask(relation, tb.gt(first, second));
        } else if (firstCEValue < secondCEValue) {
            createInsertedTask(relation, tb.gt(first, second));
            createInsertedTask(relation, tb.geq(first, second));
            createInsertedTask(relation, tb.equals(first, second));
        } else {
            createInsertedTask(relation, tb.lt(first, second));
            createInsertedTask(relation, tb.leq(first, second));
            createInsertedTask(relation, tb.equals(first, second));
        }
    }

    private void createInsertedTask(Tuple<Term, Term> source, JTerm term) throws InterruptedException {
        CandidateInvariant extendedCandidate = new CandidateInvariant(candidateInvariant);
        extendedCandidate.addConjunct(source, term);
        createExtendedTask(extendedCandidate);
    }

    private void createInsertedTask(Term source, Term term) throws InterruptedException {
        createInsertedTask(source, Conjunct.create(term, services));
    }

    private void createInsertedTask(Term source, Conjunct conjunct) throws InterruptedException {
        CandidateInvariant extendedCandidate = new CandidateInvariant(candidateInvariant);
        extendedCandidate.addConjunct(source, conjunct);
        createExtendedTask(extendedCandidate);
    }

    private void createExtendedTask(CandidateInvariant extendedCandidate) throws InterruptedException {
        if (!traversedCandidates.contains(extendedCandidate) && !extendedCandidate.repeatingHistory()) {
            taskQueue.put(extendedCandidate);
            traversedCandidates.add(extendedCandidate);
            addedInRun++;
        }
    }

    @Override
    public String toString() {
        return candidateInvariant.toString();
    }
}
