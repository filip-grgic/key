package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.SMTResult;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Tuple;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.VerificationCondition;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.util.*;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

public class CandidateGenerationTask implements Runnable {

    private final Services services;
    private final List<VerificationCondition> initiationVCs;
    private final List<VerificationCondition> consecComplVCs;
    private CandidateInvariant candidateInvariant;
    private final AtomicBoolean isFinished;
    private final AtomicReference<Term> loopInvariant;
    private final BlockingQueue<CandidateInvariant> taskQueue;
    private final Set<CandidateInvariant> traversedCandidates;
    private final int id;

    public CandidateGenerationTask(Services services, AtomicBoolean isFinished, AtomicReference<Term> loopInvariant, BlockingQueue<CandidateInvariant> taskQueue, Set<CandidateInvariant> traversedCandidates, List<VerificationCondition> verificationConditions, int id) {
        this.services = services;
        this.initiationVCs = verificationConditions.stream().filter(vc -> vc.getVCKind() == VerificationCondition.VCKind.INITIATION).toList();
        this.consecComplVCs = verificationConditions.stream().filter(vc -> vc.getVCKind() == VerificationCondition.VCKind.COMPLETION || vc.getVCKind() == VerificationCondition.VCKind.CONSECUTION).toList();
        this.isFinished = isFinished;
        this.loopInvariant = loopInvariant;
        this.taskQueue = taskQueue;
        this.traversedCandidates = traversedCandidates;
        this.id = id;
    }

    @Override
    public void run() {
        try {
            int i;
            int considered = 0;

            while (!isFinished.get()) {
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
                considered++;

                if (checkVerificationConditions()) {
                    loopInvariant.set(candidateInvariant.translateToTerm());
                    isFinished.set(true);
                    System.out.println("Finished generation after " + considered + " candidates");
                    System.out.println("Candidate has " + candidateInvariant.getHistorySize() + " history entries");
                    System.out.println(taskQueue.size() + " candidates left in queue");
                }
            }
        } catch (InterruptedException e) {
            this.notify();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    /**
     * Check if the verification conditions are fulfilled for the current candidate invariant.
     * @return true if the verification conditions are fulfilled, false otherwise.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private boolean checkVerificationConditions() throws InterruptedException {

        //Check if the initiation verification conditions are fulfilled
        //Stop the analysis of the current candidate if initiation is not fulfilled
        for (VerificationCondition vc : initiationVCs) {
            SMTResult result = vc.checkFulfillment(candidateInvariant.translateToTerm());
            if (!result.isValid()) {
                return false;
            }
        }

        boolean checksAllVCs = true;

        //Check if the consecution and completion verification conditions are fulfilled
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

    /**
     * Handles the situation where the consecution verification condition is not fulfilled.
     * @param vc the consecution verification condition that is not fulfilled.
     * @param result the result of the consecution verification condition.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void handleConsecutionCounterexample(VerificationCondition vc, SMTResult result) throws InterruptedException {
        insertRelatedTerms(vc.getAntecedentRelations(), result, true);
        insertRelatedTerms(vc.getSuccedentRelations(), result, false);
        insertQuantifiedTerms(vc);
    }

    /**
     * Handles the situation where the completion verification condition is not fulfilled.
     * @param vc the completion verification condition that is not fulfilled.
     * @param result the result of the completion verification condition.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void handleCompletionCounterexample(VerificationCondition vc, SMTResult result) throws InterruptedException {
        for (Term succedentTerm : vc.getSuccedentTerms()) {
            if (candidateInvariant.containsSource(succedentTerm)) {
                continue;
            }
            createInsertedTask(succedentTerm, succedentTerm);

            handleEqualities(vc, succedentTerm);
        }

        insertQuantifiedTerms(vc);
        insertRelatedTerms(vc.getAntecedentRelations(), result, true);
        insertRelatedTerms(vc.getSuccedentRelations(), result, false);
    }

    /**
     * Creates the extension using equality pairs collected from the candidate invariant and the antecedent of the verification condition.
     * The extension is inserted into the task queue.
     *
     * @param vc the verification condition.
     * @param succedentTerm the term of the succedent of the verification condition.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void handleEqualities(VerificationCondition vc, Term succedentTerm) throws InterruptedException {
        Set<Tuple<Term, Term>> equalities = candidateInvariant.collectEqualities(vc.getAntecedentTerms());
        for (Tuple<Term, Term> equality : equalities) {
            Term replaced1 = services.getTermBuilder().replaceContainingTerm(succedentTerm, equality.first(), equality.second());
            Term replaced2 = services.getTermBuilder().replaceContainingTerm(succedentTerm, equality.second(), equality.first());
            createInsertedTask(succedentTerm, replaced1);
            createInsertedTask(succedentTerm, replaced2);
        }
    }

    /**
     * Inserts the related terms of the verification condition into the task queue.
     * If the counterexample is usable for insertion, they are inserted heuristically.
     * Otherwise, they are inserted naively.
     *
     * @param relations the relations of the verification condition.
     * @param result the result of checking the fulfillment of the verification condition.
     * @param inAnte true if the verification condition is an antecedent, false if it is a succedent.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void insertRelatedTerms(List<Tuple<Term, Term>> relations, SMTResult result, boolean inAnte) throws InterruptedException {
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();

        for (Tuple<Term, Term> relation : relations) {

            if (candidateInvariant.containsSource(relation) || relation.first().sort().equals(heapSort) || relation.second().sort().equals(heapSort)) {
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

    /**
     * Inserts the related terms of the verification condition into the task queue naively.
     *
     * @param relation the relation of the verification condition for marking the source of the insertion.
     * @param first 1st term of the relation.
     * @param second 2nd term of the relation.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void insertNaively(Tuple<Term, Term> relation, JTerm first, JTerm second) throws InterruptedException {
        TermBuilder tb = services.getTermBuilder();

        createInsertedTask(relation, tb.equals(first, second));
        createInsertedTask(relation, tb.geq(first, second));
        createInsertedTask(relation, tb.leq(first, second));
        createInsertedTask(relation, tb.gt(first, second));
        createInsertedTask(relation, tb.lt(first, second));
    }

    /**
     * Inserts the related terms of the verification condition into the task queue heuristically based on the counterexample.
     * @param relation the relation of the verification condition for marking the source of the insertion.
     * @param counterexample the counterexample of the verification condition.
     * @param first 1st term of the relation.
     * @param second 2nd term of the relation.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
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

    /**
     * Inserts the related terms of the verification condition into the task queue heuristically based on the counterexample.
     * The relation is inserted inversely if the relation was sourced in the succedent of the verification condition.
     *
     * @param relation the relation of the verification condition for marking the source of the insertion.
     * @param counterexample the counterexample of the verification condition.
     * @param first 1st term of the relation.
     * @param second 2nd term of the relation.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
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

    /**
     * Inserts quantified terms of the verification condition into the task queue and implementing the existentiality
     * narrowing extension.
     * @param vc the verification condition.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void insertQuantifiedTerms(VerificationCondition vc) throws InterruptedException {
        List<Term> antecedentTerms = vc.getAntecedentTerms();

        for (Term antecedentTerm : antecedentTerms) {
            if (candidateInvariant.containsSource(antecedentTerm)) {
                continue;
            }
            if (antecedentTerm.op().equals(Quantifier.EX)) {
                BoundConjunct conjunct = (BoundConjunct) Conjunct.create(antecedentTerm, services);
                Map<Term, VariableBounds> boundedTerms = conjunct.getQuantifiableVariableBounds();
                for (Term boundedTerm : boundedTerms.keySet()) {
                    VariableBounds bounds = boundedTerms.get(boundedTerm); //b1 and b2
                    Map<Term, Set<Term>> newLowerBounds = new HashMap<>();
                    Map<Term, Set<Term>> newUpperBounds = new HashMap<>();

                    for (Term lowerBound : bounds.getAllLowerBounds()) {
                        Set<Term> lowerReplacements = new HashSet<>(vc.getBounds(lowerBound).getAllUpperBounds());
                        lowerReplacements.addAll(candidateInvariant.getBounds(lowerBound).getAllUpperBounds());
                        for (Term lowerReplacement : lowerReplacements) {
                            if (!newLowerBounds.containsKey(lowerReplacement)) {
                                newLowerBounds.put(lowerReplacement, new HashSet<>());
                            }
                            newLowerBounds.get(lowerReplacement).add(lowerBound);
                        }

                    }

                    for (Term upperBound : bounds.getAllUpperBounds()) {
                        Set<Term> upperReplacements = new HashSet<>(vc.getBounds(upperBound).getAllLowerBounds());
                        upperReplacements.addAll(candidateInvariant.getBounds(upperBound).getAllLowerBounds());
                        for (Term upperReplacement : upperReplacements) {
                            if (!newUpperBounds.containsKey(upperReplacement)) {
                                newUpperBounds.put(upperReplacement, new HashSet<>());
                            }
                            newUpperBounds.get(upperReplacement).add(upperBound);
                        }

                    }

                    for (Term newLowerBound : newLowerBounds.keySet()) {
                        for (Term newUpperBound : newUpperBounds.keySet()) {
                            BoundConjunct boundConjunct1 = new BoundConjunct(conjunct);
                            for (Term newLowerBoundReplacement : newLowerBounds.get(newLowerBound)) {
                                boundConjunct1 = (BoundConjunct) boundConjunct1.replace(newLowerBoundReplacement, newUpperBound);
                            }
                            
                            BoundConjunct boundConjunct2 = new BoundConjunct(conjunct);
                            for (Term newUpperBoundReplacement : newUpperBounds.get(newUpperBound)) {
                                boundConjunct2 = (BoundConjunct) boundConjunct2.replace(newUpperBoundReplacement, newLowerBound);
                            }

                            DoubleBoundConjunct doubleBoundConjunct = new DoubleBoundConjunct(boundConjunct1, boundConjunct2, services, true);
                            createInsertedTask(antecedentTerm, doubleBoundConjunct);
                        }
                    }
                }
            }
        }
    }

    /**
     * Creates a new task for the given relation source and term.
     * @param source the relation source.
     * @param term the relation term.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void createInsertedTask(Tuple<Term, Term> source, JTerm term) throws InterruptedException {
        CandidateInvariant extendedCandidate = new CandidateInvariant(candidateInvariant);
        extendedCandidate.addConjunct(source, term);
        createExtendedTask(extendedCandidate);
    }

    /**
     * Creates a new task for the given semantic source and term.
     * @param source the semantic source.
     * @param term the semantic term.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void createInsertedTask(Term source, Term term) throws InterruptedException {
        createInsertedTask(source, Conjunct.create(term, services));
    }

    /**
     * Creates a new task for the given semantic source and conjunct.
     * @param source the semantic source.
     * @param conjunct the semantic conjunct.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void createInsertedTask(Term source, Conjunct conjunct) throws InterruptedException {
        CandidateInvariant extendedCandidate = new CandidateInvariant(candidateInvariant);
        extendedCandidate.addConjunct(source, conjunct);
        createExtendedTask(extendedCandidate);
    }

    /**
     * Creates a new task for the given candidate invariant if it is not already in the task queue.
     * @param extendedCandidate the candidate invariant to be added to the task queue.
     * @throws InterruptedException if the thread is interrupted while waiting for the result of the verification conditions.
     */
    private void createExtendedTask(CandidateInvariant extendedCandidate) throws InterruptedException {
        if (!traversedCandidates.contains(extendedCandidate) && !extendedCandidate.repeatingHistory()) {
            taskQueue.put(extendedCandidate);
            traversedCandidates.add(extendedCandidate);
        }
    }

    @Override
    public String toString() {
        return candidateInvariant.toString();
    }
}
