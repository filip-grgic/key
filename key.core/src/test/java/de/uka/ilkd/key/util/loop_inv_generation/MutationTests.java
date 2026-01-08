package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TestJavaInfo;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.loop_inv_generation.mutations.*;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

public class MutationTests {

    private Services services;
    private TermBuilder termBuilder;
    private JTerm one;
    private JTerm two;
    private LocationVariable xVar;
    private LocationVariable yVar;
    private LocationVariable zVar;
    private Term xTerm;
    private Term yTerm;
    private Term zTerm;

    private Term zLessThanXTerm;
    private Term xLessThanYTerm;
    private Term oneLessThanTwoTerm;

    private LoopInvariantFreeGen zLessThanXGen;
    private LoopInvariantFreeGen xLessThanYGen;
    private LoopInvariantFreeGen oneLessThanTwoGen;

    private LoopInvariantFreeGenome genome1;
    private LoopInvariantFreeGenome genome2;
    private LoopInvariantFreeGenome genomeTwoConjuncts;
    private LoopInvariantFreeGenome genomeWithoutVars;

    private Term[] termPool;
    private Term xPlusOneLessThanY;
    private Term zLessThanOne;

    private Set<LocationVariable> locationVariableSet;
    private Set<LocationVariable> onlyZVarSet;
    private Set<LocationVariable> xZVarSet;

    @BeforeEach
    public void setUp() {
        HelperClassForTests helper = new HelperClassForTests();
        final ProofAggregate agg = helper.parse(new File(TestJavaInfo.testfile));
        services = agg.getFirstProof().getServices();
        termBuilder = services.getTermBuilder();

        this.one = termBuilder.zTerm(1);
        this.two = termBuilder.zTerm(2);
        Sort integerSort = services.getTypeConverter().getIntegerLDT().targetSort();
        xVar = termBuilder.locationVariable("x", integerSort, true);
        yVar = termBuilder.locationVariable("y", integerSort, true);
        zVar = termBuilder.locationVariable("z", integerSort, true);

        locationVariableSet = new HashSet<>();
        locationVariableSet.add(xVar);
        locationVariableSet.add(yVar);
        locationVariableSet.add(zVar);

        onlyZVarSet = new HashSet<>();
        onlyZVarSet.add(zVar);

        xZVarSet = new HashSet<>();
        xZVarSet.add(xVar);
        xZVarSet.add(zVar);

        xTerm = termBuilder.var(xVar);
        yTerm = termBuilder.var(yVar);
        zTerm = termBuilder.var(zVar);

        xPlusOneLessThanY = termBuilder.lt(termBuilder.add((JTerm) xTerm, one), (JTerm) yTerm);
        zLessThanOne = termBuilder.lt((JTerm) zTerm, one);

        termPool = new Term[]{xPlusOneLessThanY, zLessThanOne};

        zLessThanXTerm = termBuilder.lt((JTerm) zTerm, (JTerm) xTerm);
        xLessThanYTerm = termBuilder.lt((JTerm) xTerm, (JTerm) yTerm);
        oneLessThanTwoTerm = termBuilder.lt(one, two);

        zLessThanXGen = new LoopInvariantFreeGen(services, zLessThanXTerm);
        xLessThanYGen = new LoopInvariantFreeGen(services, xLessThanYTerm);
        oneLessThanTwoGen = new LoopInvariantFreeGen(services, oneLessThanTwoTerm);

        genome1 = new LoopInvariantFreeGenome(services);
        List<LoopInvariantFreeGen> conjunct = new ArrayList<>();
        conjunct.add(zLessThanXGen);
        conjunct.add(xLessThanYGen);

        genome1.addConjunct(conjunct);

        genome2 = new LoopInvariantFreeGenome(services);
        LoopInvariantFreeGen gen2 = new LoopInvariantFreeGen(services, termBuilder.lt(one, (JTerm) yTerm));
        genome2.addConjunct(gen2);

        genomeTwoConjuncts = new LoopInvariantFreeGenome(services);
        genomeTwoConjuncts.addConjunct(gen2);
        genomeTwoConjuncts.addConjunct(xLessThanYGen);

        genomeWithoutVars = new LoopInvariantFreeGenome(services);
        genomeWithoutVars.addConjunct(oneLessThanTwoGen);
    }

    @Test
    public void testAddConjunctMutation_negativeSuitability() {
        Mutation mutation1 = new AddConjunctMutation(services, null);
        Mutation mutation2 = new AddConjunctMutation(services, new Term[]{});

        assertFalse(mutation1.suitableForMutation(genome1));
        assertFalse(mutation2.suitableForMutation(genome1));
    }

    @Test
    public void testAddConjunctMutation_positive() {
        Mutation mutation = new AddConjunctMutation(services, termPool);
        assertTrue(mutation.suitableForMutation(genomeTwoConjuncts));
        assertEquals(2, genomeTwoConjuncts.size());

        List<List<LoopInvariantFreeGen>> conjunctsCopy = new ArrayList<>(genomeTwoConjuncts.getConjuncts());

        mutation.mutate(genomeTwoConjuncts);

        assertEquals(2, conjunctsCopy.size());
        assertEquals(3, genomeTwoConjuncts.size());

        List<LoopInvariantFreeGen> newConjunct = null;

        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            if (!conjunctsCopy.contains(conjunct)) {
                newConjunct = conjunct;
            } else {
                conjunctsCopy.remove(conjunct);
            }
        }

        assertTrue(conjunctsCopy.isEmpty());
        assertNotNull(newConjunct);

        boolean isTermFromPool = false;

        for (Term term: termPool) {
            if (term.equals(newConjunct.getFirst().getTerm())) {
                isTermFromPool = true;
            }
        }

        assertTrue(isTermFromPool);
    }

    @Test
    public void testAddDisjunctMutation_negativeSuitability() {
        Mutation mutation1 = new AddDisjunctMutation(services, null);
        Mutation mutation2 = new AddDisjunctMutation(services, new Term[]{});
        assertFalse(mutation1.suitableForMutation(genome1));
        assertFalse(mutation2.suitableForMutation(genome1));
    }

    @Test
    public void testAddDisjunctMutation_positive() {
        Mutation mutation = new AddDisjunctMutation(services, termPool);
        assertTrue(mutation.suitableForMutation(genomeTwoConjuncts));
        assertEquals(2, genomeTwoConjuncts.size());

        List<List<LoopInvariantFreeGen>> conjunctsCopy = new ArrayList<>(genomeTwoConjuncts.getConjuncts());

        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            assertEquals(1, conjunct.size());
        }

        mutation.mutate(genomeTwoConjuncts);

        assertEquals(2, genomeTwoConjuncts.size());
        List<LoopInvariantFreeGen> mutatedConjunct = null;

        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            if (conjunct.size() != 1) {
                assertEquals(2, conjunct.size());
                mutatedConjunct = conjunct;
                continue;
            }

            assertEquals(1, conjunct.size());
            conjunctsCopy.remove(conjunct);
        }

        assertEquals(1, conjunctsCopy.size());

        boolean isInTermPool = false;
        for (Term term: termPool) {
            for (LoopInvariantFreeGen disjunct : mutatedConjunct) {
                if (disjunct.getTerm().equals(term)) {
                    isInTermPool = true;
                }
            }
        }

        assertTrue(isInTermPool);
    }

    @Test
    public void testDeleteConjunctMutation_negativeSuitability() {
        Mutation mutation = new DeleteConjunctMutation();
        assertFalse(mutation.suitableForMutation(genome1));
        assertFalse(mutation.suitableForMutation(genome2));
    }

    @Test
    public void testDeleteConjunctMutation_positive() {
        Mutation mutation = new DeleteConjunctMutation();
        assertTrue(mutation.suitableForMutation(genomeTwoConjuncts));
        assertEquals(2, genomeTwoConjuncts.size());

        var conjunctsCopy = new ArrayList<>(genomeTwoConjuncts.getConjuncts());

        mutation.mutate(genomeTwoConjuncts);

        assertEquals(1, genomeTwoConjuncts.size());

        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            assertTrue(conjunctsCopy.contains(conjunct));
        }

    }

    @Test
    public void testDeleteDisjunctMutation_negativeSuitability() {
        Mutation mutation = new DeleteDisjunctMutation();
        assertFalse(mutation.suitableForMutation(genome2));
    }

    @Test
    public void testDeleteDisjunctMutation_positive() {
        Mutation mutation = new DeleteDisjunctMutation();
        assertTrue(mutation.suitableForMutation(genomeTwoConjuncts));
        assertEquals(2, genomeTwoConjuncts.size());

        var conjunctsCopy = new ArrayList<>(genomeTwoConjuncts.getConjuncts());

        mutation.mutate(genomeTwoConjuncts);

        assertEquals(1, genomeTwoConjuncts.size());

        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            assertTrue(conjunctsCopy.contains(conjunct));
        }

        assertTrue(mutation.suitableForMutation(genome1));
        assertEquals(1, genome1.size());

        for (List<LoopInvariantFreeGen> conjunct : genome1.getConjuncts()) {
            assertEquals(2, conjunct.size());
        }

//        var conjunctCopy2 = new ArrayList<>(genome1.getConjuncts().getFirst());
        var conjunctCopy2 = genome1.copy().getConjuncts().getFirst();

        mutation.mutate(genome1);

        assertEquals(1, genome1.size());
        assertEquals(1, genome1.getConjuncts().getFirst().size());
    }

    @Test
    public void testNegateConjunctMutation_negativeSuitability() {
        Mutation mutation = new NegateConjunctMutation();
        assertFalse(mutation.suitableForMutation(new LoopInvariantFreeGenome(services)));
    }

    @Test
    public void testNegateConjunctMutation_positiveTwoSingleDisjunctConjuncts() {
        Mutation mutation = new NegateConjunctMutation();
        assertTrue(mutation.suitableForMutation(genomeTwoConjuncts));
        assertEquals(2, genomeTwoConjuncts.size());
        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            assertEquals(1, conjunct.size());
        }

        LoopInvariantFreeGenome genomeTwoConjunctsCopy = genomeTwoConjuncts.copy();

        mutation.mutate(genomeTwoConjuncts);

        assertEquals(2, genomeTwoConjunctsCopy.size());
        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            assertEquals(1, conjunct.size());
        }

        int differingPolarities = 0;

        List<Term> collectedTermsInCopy = new ArrayList<>();

        for (int i = 0; i < genomeTwoConjunctsCopy.getConjuncts().size(); i++) {
            for (int j = 0; j < genomeTwoConjunctsCopy.getConjuncts().get(i).size(); j++) {
                collectedTermsInCopy.add(genomeTwoConjunctsCopy.getConjuncts().get(i).get(j).getTerm());
                if (genomeTwoConjunctsCopy.getConjuncts().get(i).get(j).isNegated()) {
                    differingPolarities++;
                }
            }
        }

        for (int i = 0; i < genomeTwoConjuncts.getConjuncts().size(); i++) {
            for (int j = 0; j < genomeTwoConjuncts.getConjuncts().get(i).size(); j++) {
                assertTrue(collectedTermsInCopy.contains(genomeTwoConjuncts.getConjuncts().get(i).get(j).getTerm()));
                if (genomeTwoConjuncts.getConjuncts().get(i).get(j).isNegated()) {
                    differingPolarities--;
                }
            }
        }

        assertEquals(1, differingPolarities*differingPolarities);

    }

    @Test
    public void testNegateConjunctMutation_positiveOneDualDisjunctConjunct() {
        Mutation mutation = new NegateConjunctMutation();
        assertTrue(mutation.suitableForMutation(genome1));
        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjunctSize(0));
        List<Term> terms = new ArrayList<>();
        for (LoopInvariantFreeGen disjunct : genome1.getConjuncts().getFirst()) {
            assertFalse(disjunct.isNegated());
            terms.add(disjunct.getTerm());
        }

        mutation.mutate(genome1);

        assertEquals(2, genome1.size());
        for (List<LoopInvariantFreeGen> conjunct : genome1.getConjuncts()) {
            assertEquals(1, conjunct.size());
            assertTrue(terms.contains(conjunct.getFirst().getTerm()));
            assertTrue(conjunct.getFirst().isNegated());
        }

    }

    @Test
    public void testNegateDisjunctMutation_negativeSuitability() {
        Mutation mutation = new NegateDisjunctMutation();
        assertFalse(mutation.suitableForMutation(new LoopInvariantFreeGenome(services)));
    }

    @Test
    public void testNegateDisjunctMutation_positiveTwoSingleDisjunctConjuncts() {
        Mutation mutation = new NegateDisjunctMutation();
        assertTrue(mutation.suitableForMutation(genomeTwoConjuncts));
        assertEquals(2, genomeTwoConjuncts.size());
        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            assertEquals(1, conjunct.size());
        }

        LoopInvariantFreeGenome genomeTwoConjunctsCopy = genomeTwoConjuncts.copy();

        mutation.mutate(genomeTwoConjuncts);

        assertEquals(2, genomeTwoConjunctsCopy.size());
        for (List<LoopInvariantFreeGen> conjunct : genomeTwoConjuncts.getConjuncts()) {
            assertEquals(1, conjunct.size());
        }

        int differingPolarities = 0;

        for (int i = 0; i < genomeTwoConjunctsCopy.getConjuncts().size(); i++) {
            for (int j = 0; j < genomeTwoConjunctsCopy.getConjuncts().get(i).size(); j++) {
                assertEquals(genomeTwoConjunctsCopy.getConjuncts().get(i).get(j).getTerm(), genomeTwoConjuncts.getConjuncts().get(i).get(j).getTerm());
                if (genomeTwoConjunctsCopy.getConjuncts().get(i).get(j).isNegated() ^ genomeTwoConjuncts.getConjuncts().get(i).get(j).isNegated()) {
                    differingPolarities++;
                }
            }
        }

        assertEquals(1, differingPolarities);

    }

    @Test
    public void testNegateDisjunctMutation_positiveOneDualDisjunctConjunct() {
        Mutation mutation = new NegateDisjunctMutation();
        assertTrue(mutation.suitableForMutation(genome1));
        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjunctSize(0));
        for (LoopInvariantFreeGen disjunct : genome1.getConjuncts().getFirst()) {
            assertFalse(disjunct.isNegated());
        }

        LoopInvariantFreeGenome genome1Copy = genome1.copy();

        mutation.mutate(genome1);

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjunctSize(0));

        int differingPolarities = 0;

        for (int i = 0; i < genome1Copy.getConjuncts().size(); i++) {
            for (int j = 0; j < genome1Copy.getConjuncts().get(i).size(); j++) {
                assertEquals(genome1Copy.getConjuncts().get(i).get(j).getTerm(), genome1.getConjuncts().get(i).get(j).getTerm());
                if (genome1Copy.getConjuncts().get(i).get(j).isNegated() ^ genome1.getConjuncts().get(i).get(j).isNegated()) {
                    differingPolarities++;
                }
            }
        }

        assertEquals(1, differingPolarities);
    }

    @Test
    public void testReplaceVariableMutation_negativeSuitability() {
        Mutation mutation = new ReplaceVariableMutation(locationVariableSet);
        assertFalse(mutation.suitableForMutation(new LoopInvariantFreeGenome(services)));
        assertFalse(mutation.suitableForMutation(genomeWithoutVars));
    }

    @Test
    public void testReplaceVariableMutation_positive() {
        Mutation xZMutation = new ReplaceVariableMutation(xZVarSet);
        assertTrue(xZMutation.suitableForMutation(genome2));
        assertFalse(genome2.containsProgramVariable(xVar));
        assertTrue(genome2.containsProgramVariable(yVar));
        assertFalse(genome2.containsProgramVariable(zVar));

        int variableSetSize = genome2.getProgramVariableNameSet().size();
        xZMutation.mutate(genome2);

        assertEquals(variableSetSize, genome2.getProgramVariableNameSet().size());
        assertFalse(genome2.containsProgramVariable(yVar));
        assertTrue(genome2.containsProgramVariable(xVar) || genome2.containsProgramVariable(zVar));

        Mutation onlyZMutation = new ReplaceVariableMutation(onlyZVarSet);
        assertTrue(onlyZMutation.suitableForMutation(genomeTwoConjuncts));
        assertTrue(genomeTwoConjuncts.containsProgramVariable(xVar));
        assertTrue(genomeTwoConjuncts.containsProgramVariable(yVar));
        assertFalse(genomeTwoConjuncts.containsProgramVariable(zVar));

        variableSetSize = genomeTwoConjuncts.getProgramVariableNameSet().size();
        onlyZMutation.mutate(genomeTwoConjuncts);

        assertEquals(variableSetSize, genomeTwoConjuncts.getProgramVariableNameSet().size());
        assertTrue(genomeTwoConjuncts.containsProgramVariable(xVar) ^ genomeTwoConjuncts.containsProgramVariable(yVar));
        assertTrue(genomeTwoConjuncts.containsProgramVariable(zVar));

    }

}
