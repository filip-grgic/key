package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TestJavaInfo;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGen;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.BeforeEach;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import static org.junit.jupiter.api.Assertions.*;

import java.io.File;

class LoopInvariantFreeGenTests {

    private Services services;
    private TermBuilder termBuilder;
    private JTerm one;
    private JTerm two;
    private LocationVariable xVar;
    private LocationVariable yVar;
    private LocationVariable zVar;

    private LocationVariable nullLocVariable;

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

        nullLocVariable = null;
    }

    @Test
    public void testConstructor_positive_affirmativeLeq() {
        Term term = termBuilder.leq(one, two);
        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, term);

        assertFalse(gen.isNegated());
        assertEquals(gen.getTerm(), term);
        assertEquals(gen.getLeft(), one);
        assertEquals(gen.getRight(), two);
    }

    @Test
    public void testConstructor_positive_testAffirmativeLessThan() {
        Term term = termBuilder.lt(one, two);
        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, term);

        assertFalse(gen.isNegated());
        assertEquals(gen.getTerm(), term);
        assertEquals(gen.getLeft(), one);
        assertEquals(gen.getRight(), two);
    }

    @Test
    public void testConstructor_positive_testNonAffirmativeLeq() {
        JTerm term = termBuilder.leq(one, two);
        Term negatedTerm = termBuilder.not(term);
        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, negatedTerm);

        assertTrue(gen.isNegated());
        assertEquals(gen.getTerm(), term);
        assertEquals(gen.getLeft(), one);
        assertEquals(gen.getRight(), two);
    }

    @Test
    public void testConstructor_positive_testNonAffirmativeLessThan() {
        JTerm term = termBuilder.lt(one, two);
        Term negatedTerm = termBuilder.not(term);
        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, negatedTerm);

        assertTrue(gen.isNegated());
        assertEquals(gen.getTerm(), term);
        assertEquals(gen.getLeft(), one);
        assertEquals(gen.getRight(), two);
    }

    @Test
    public void testConstructor_positive_testVariableNames() {
        Term term = termBuilder.lt(termBuilder.var(xVar), two);
        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, term);

        assertTrue(gen.containsProgramVariable(xVar));
        assertFalse(gen.containsProgramVariable(yVar));
        assertFalse(gen.containsProgramVariable(nullLocVariable));
    }

    @Test
    public void testConstructor_positive_testAdditionSubTerm() {
        JTerm xTerm = termBuilder.var(xVar);
        JTerm right = termBuilder.add(termBuilder.add(one, xTerm), two);
        JTerm left = termBuilder.var(yVar);
        Term term = termBuilder.lt(left, right);

        assertDoesNotThrow(() -> new LoopInvariantFreeGen(services, term));

        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, term);

        assertEquals(gen.getTerm(), term);
        assertTrue(gen.containsProgramVariable(xVar));
        assertTrue(gen.containsProgramVariable(yVar));
    }

    @Test
    public void testConstructor_negative_testGreaterThan() {
        assertThrows(IllegalArgumentException.class, () -> {
                JTerm term = termBuilder.gt(one, two);
                new LoopInvariantFreeGen(services, term);
        });
    }

    @Test
    public void testReplaceProgramVariable_positive() {
        JTerm xTerm = termBuilder.var(xVar);
        JTerm yTerm = termBuilder.var(yVar);
        Term term1 = termBuilder.lt(xTerm, two);
        Term term2 = termBuilder.lt(yTerm, two);

        LoopInvariantFreeGen gen1 =  new LoopInvariantFreeGen(services, term1);

        assertEquals(gen1.getTerm(), term1);
        assertNotEquals(gen1.getTerm(), term2);
        assertTrue(gen1.containsProgramVariable(xVar));
        assertFalse(gen1.containsProgramVariable(yVar));

        gen1.replaceProgramVariable(xVar, yVar);

        assertEquals(gen1.getTerm(), term2);
        assertNotEquals(gen1.getTerm(), term1);
        assertFalse(gen1.containsProgramVariable(xVar));
        assertTrue(gen1.containsProgramVariable(yVar));
    }

    @Test
    public void testReplaceProgramVariable_nonExistingVariable() {
        JTerm xTerm = termBuilder.var(xVar);
        Term term1 = termBuilder.lt(xTerm, two);

        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, term1);

        assertEquals(gen.getTerm(), term1);
        assertTrue(gen.containsProgramVariable(xVar));
        assertFalse(gen.containsProgramVariable(yVar));
        assertFalse(gen.containsProgramVariable(zVar));

        gen.replaceProgramVariable(yVar, zVar);

        assertEquals(gen.getTerm(), term1);
        assertTrue(gen.containsProgramVariable(xVar));
        assertFalse(gen.containsProgramVariable(yVar));
        assertFalse(gen.containsProgramVariable(zVar));
    }

    @Test
    public void testReplaceProgramVariable_nullParameter() {
        JTerm xTerm = termBuilder.var(xVar);
        Term term1 = termBuilder.lt(xTerm, two);

        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, term1);

        assertEquals(gen.getTerm(), term1);
        assertTrue(gen.containsProgramVariable(xVar));

        gen.replaceProgramVariable(xVar, null);

        assertEquals(gen.getTerm(), term1);
        assertTrue(gen.containsProgramVariable(xVar));

        gen.replaceProgramVariable(nullLocVariable, yVar);

        assertEquals(gen.getTerm(), term1);
        assertTrue(gen.containsProgramVariable(xVar));
        assertFalse(gen.containsProgramVariable(yVar));
    }

    @Test
    public void testReplaceProgramVariable_additionSubTerm() {
        JTerm xTerm = termBuilder.var(xVar);
        JTerm zTerm = termBuilder.var(zVar);
        JTerm rightX = termBuilder.add(termBuilder.add(one, xTerm), two);
        JTerm rightZ = termBuilder.add(termBuilder.add(one, zTerm), two);
        JTerm leftX = termBuilder.var(xVar);
        JTerm leftY = termBuilder.var(yVar);
        Term term1 = termBuilder.lt(leftY, rightX);

        LoopInvariantFreeGen gen = new LoopInvariantFreeGen(services, term1);

        assertEquals(gen.getTerm(), term1);
        assertTrue(gen.containsProgramVariable(xVar));
        assertTrue(gen.containsProgramVariable(yVar));
        assertFalse(gen.containsProgramVariable(zVar));

        gen.replaceProgramVariable(xVar, zVar);
        Term term2 = termBuilder.lt(leftY, rightZ);

        assertEquals(gen.getTerm(), term2);
        assertFalse(gen.containsProgramVariable(xVar));
        assertTrue(gen.containsProgramVariable(yVar));
        assertTrue(gen.containsProgramVariable(zVar));

        gen.replaceProgramVariable(yVar, xVar);
        Term term3 = termBuilder.lt(leftX, rightZ);

        assertEquals(gen.getTerm(), term3);
        assertTrue(gen.containsProgramVariable(xVar));
        assertFalse(gen.containsProgramVariable(yVar));
        assertTrue(gen.containsProgramVariable(zVar));
    }

}
