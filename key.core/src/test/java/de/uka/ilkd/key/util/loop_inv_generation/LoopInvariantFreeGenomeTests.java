package de.uka.ilkd.key.util.loop_inv_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TestJavaInfo;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGen;
import de.uka.ilkd.key.util.loop_inv_generation.structures.LoopInvariantFreeGenome;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.key_project.logic.Term;
import org.key_project.logic.sort.Sort;

import static org.junit.jupiter.api.Assertions.*;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class LoopInvariantFreeGenomeTests {

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

    private LoopInvariantFreeGen zLessThanX;
    private LoopInvariantFreeGen xLessThanY;

    private LoopInvariantFreeGenome genome1;
    private LoopInvariantFreeGenome genome2;
    private LoopInvariantFreeGenome genomeTwoConjuncts;

    private LoopInvariantFreeGen oneLessThanTwo;

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

        xTerm = termBuilder.var(xVar);
        yTerm = termBuilder.var(yVar);
        zTerm = termBuilder.var(zVar);

        zLessThanX = new LoopInvariantFreeGen(services, termBuilder.lt((JTerm) zTerm, (JTerm) xTerm));
        xLessThanY = new LoopInvariantFreeGen(services, termBuilder.lt((JTerm) xTerm, (JTerm) yTerm));
        oneLessThanTwo = new LoopInvariantFreeGen(services, termBuilder.lt(one, two));
    }

    @Test
    public void testConstructor_positive() {
        LoopInvariantFreeGenome genome = new LoopInvariantFreeGenome(services);
        assertNotNull(genome);
        assertNotNull(genome.getConjuncts());
        assertEquals(0, genome.size());
    }

    @Test
    public void testAddConjunct_positiveWithList() {
        LoopInvariantFreeGenome genome = new LoopInvariantFreeGenome(services);

        List<LoopInvariantFreeGen> conjunct = new ArrayList<>();
        conjunct.add(zLessThanX);
        conjunct.add(xLessThanY);

        genome.addConjunct(conjunct);

        assertEquals(1, genome.size());
        assertEquals(conjunct, genome.getConjuncts().getFirst());
        assertEquals(2, genome.getConjunctSize(0));
    }

    @Test
    public void testAddConjunct_positiveWithGen() {
        LoopInvariantFreeGenome genome = new LoopInvariantFreeGenome(services);

        genome.addConjunct(zLessThanX);

        List<LoopInvariantFreeGen> conjunct = new ArrayList<>();
        conjunct.add(zLessThanX);

        assertEquals(1, genome.size());
        assertEquals(conjunct, genome.getConjuncts().getFirst());
        assertEquals(1, genome.getConjunctSize(0));
    }

    private void setUpGenomes() {
        genome1 = new LoopInvariantFreeGenome(services);
        List<LoopInvariantFreeGen> conjunct = new ArrayList<>();
        conjunct.add(zLessThanX);
        conjunct.add(xLessThanY);

        genome1.addConjunct(conjunct);

        genome2 = new LoopInvariantFreeGenome(services);
        LoopInvariantFreeGen gen2 = new LoopInvariantFreeGen(services, termBuilder.lt(one, (JTerm) yTerm));
        genome2.addConjunct(gen2);

        genomeTwoConjuncts = new LoopInvariantFreeGenome(services);
        genomeTwoConjuncts.addConjunct(gen2);
        genomeTwoConjuncts.addConjunct(xLessThanY);
    }

    @Test
    public void testRemoveConjunct_positive() {
        setUpGenomes();

        assertEquals(1, genome1.size());
        genome1.removeConjunct(0);

        assertEquals(0, genome1.size());
    }

    @Test
    public void testRemoveConjunct_negativeOutOfBoundsIndex() {
        setUpGenomes();
        assertEquals(1, genome1.size());
        genome1.removeConjunct(10);
        assertEquals(1, genome1.size());
    }

    @Test
    public void testNegateConjunct_positiveSingleDisjunct() {
        setUpGenomes();

        assertEquals(1, genome2.size());
        assertFalse(genome2.getConjuncts().getFirst().getFirst().isNegated());
        genome2.negateConjunct(0);
        assertEquals(1, genome2.size());
        assertTrue(genome2.getConjuncts().getFirst().getFirst().isNegated());
    }

    @Test
    public void testNegateConjunct_positiveMultipleDisjuncts() {
        setUpGenomes();

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());
        assertFalse(genome1.getConjuncts().getFirst().getFirst().isNegated());
        assertFalse(genome1.getConjuncts().getFirst().get(1).isNegated());

        genome1.negateConjunct(0);

        System.out.println(genome1.getConjuncts());

        assertEquals(2, genome1.size());
        assertEquals(1, genome1.getConjuncts().getFirst().size());
        assertEquals(1, genome1.getConjuncts().get(1).size());
        assertTrue(genome1.getConjuncts().getFirst().getFirst().isNegated());
        assertTrue(genome1.getConjuncts().get(1).getFirst().isNegated());
    }

    @Test
    public void testNegateConjunct_negativeOutOfBoundsIndex() {
        setUpGenomes();

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());
        assertFalse(genome1.getConjuncts().getFirst().getFirst().isNegated());
        assertFalse(genome1.getConjuncts().getFirst().get(1).isNegated());

        genome1.negateConjunct(10);

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());
        assertFalse(genome1.getConjuncts().getFirst().getFirst().isNegated());
        assertFalse(genome1.getConjuncts().getFirst().get(1).isNegated());
    }

    @Test
    public void testAddDisjunct_positive() {
        setUpGenomes();

        assertEquals(1, genome2.size());
        assertEquals(1, genome2.getConjuncts().getFirst().size());

        genome2.addDisjunct(oneLessThanTwo, 0);

        assertEquals(1, genome2.size());
        assertEquals(2, genome2.getConjuncts().getFirst().size());
    }

    @Test
    public void testAddDisjunct_negativeOutOfBoundsIndex() {
        setUpGenomes();

        assertEquals(1, genome2.size());
        assertEquals(1, genome2.getConjuncts().getFirst().size());

        genome2.addDisjunct(oneLessThanTwo, 10);

        assertEquals(1, genome2.size());
        assertEquals(1, genome2.getConjuncts().getFirst().size());
    }

    @Test
    public void testRemoveDisjunct_positiveMultipleDisjuncts() {
        setUpGenomes();

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());

        genome1.removeDisjunct(0,0);

        assertEquals(1, genome1.size());
        assertEquals(1, genome1.getConjuncts().getFirst().size());
    }

    @Test
    public void testRemoveDisjunct_positiveSingleDisjunctMultipleConjuncts() {
        setUpGenomes();

        assertEquals(2, genomeTwoConjuncts.size());
        assertEquals(1, genomeTwoConjuncts.getConjuncts().getFirst().size());
        assertEquals(1, genomeTwoConjuncts.getConjuncts().get(1).size());

        genomeTwoConjuncts.removeDisjunct(0,0);

        assertEquals(1, genomeTwoConjuncts.size());
        assertEquals(1, genomeTwoConjuncts.getConjuncts().getFirst().size());
    }

    @Test
    public void testRemoveDisjunct_positiveSingleDisjunctSingleConjunct() {
        setUpGenomes();

        assertEquals(1, genome2.size());
        assertEquals(1, genome2.getConjuncts().getFirst().size());

        genome2.removeDisjunct(0,0);

        assertEquals(0, genome2.size());
        assertNotNull(genome2.getConjuncts());
    }

    @Test
    public void testRemoveDisjunct_negativeOutOfBoundsIndex() {
        setUpGenomes();

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());

        genome1.removeDisjunct(10,0);
        genome1.removeDisjunct(0,10);

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());
    }

    @Test
    public void testNegateDisjunct_positive() {
        setUpGenomes();

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());
        assertFalse(genome1.getConjuncts().getFirst().getFirst().isNegated());
        assertFalse(genome1.getConjuncts().getFirst().get(1).isNegated());

        genome1.negateDisjunct(0, 1);

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());
        assertFalse(genome1.getConjuncts().getFirst().getFirst().isNegated());
        assertTrue(genome1.getConjuncts().getFirst().get(1).isNegated());
    }

    @Test
    public void testNegateDisjunct_negativeOutOfBoundsIndex() {
        setUpGenomes();

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());
        assertFalse(genome1.getConjuncts().getFirst().getFirst().isNegated());
        assertFalse(genome1.getConjuncts().getFirst().get(1).isNegated());

        genome1.negateDisjunct(10, 0);
        genome1.negateDisjunct(0, 10);

        assertEquals(1, genome1.size());
        assertEquals(2, genome1.getConjuncts().getFirst().size());
        assertFalse(genome1.getConjuncts().getFirst().getFirst().isNegated());
        assertFalse(genome1.getConjuncts().getFirst().get(1).isNegated());
    }

    @Test
    public void testContainsProgramVariable_positive() {
        setUpGenomes();

        assertTrue(genome1.containsProgramVariable(xVar));
        assertTrue(genome1.containsProgramVariable(yVar));
        assertTrue(genome1.containsProgramVariable(zVar));

        assertFalse(genome2.containsProgramVariable(xVar));
        assertTrue(genome2.containsProgramVariable(yVar));
        assertFalse(genome2.containsProgramVariable(zVar));

        assertTrue(genomeTwoConjuncts.containsProgramVariable(xVar));
        assertTrue(genomeTwoConjuncts.containsProgramVariable(yVar));
        assertFalse(genomeTwoConjuncts.containsProgramVariable(zVar));
    }

    @Test
    public void testContainsProgramVariable_positiveAfterRemoval() {
        setUpGenomes();

        assertTrue(genome1.containsProgramVariable(xVar));
        assertTrue(genome1.containsProgramVariable(yVar));
        assertTrue(genome1.containsProgramVariable(zVar));

        genome1.removeDisjunct(0, 0);

        assertTrue(genome1.containsProgramVariable(xVar));
        assertTrue(genome1.containsProgramVariable(yVar));
        assertFalse(genome1.containsProgramVariable(zVar));

        genome1.removeConjunct(0);

        assertFalse(genome1.containsProgramVariable(xVar));
        assertFalse(genome1.containsProgramVariable(yVar));
        assertFalse(genome1.containsProgramVariable(zVar));

        assertTrue(genomeTwoConjuncts.containsProgramVariable(xVar));
        assertTrue(genomeTwoConjuncts.containsProgramVariable(yVar));
        assertFalse(genomeTwoConjuncts.containsProgramVariable(zVar));

        genomeTwoConjuncts.removeConjunct(1);

        assertFalse(genomeTwoConjuncts.containsProgramVariable(xVar));
        assertTrue(genomeTwoConjuncts.containsProgramVariable(yVar));
        assertFalse(genomeTwoConjuncts.containsProgramVariable(zVar));
    }

    @Test
    public void testReplaceVariable_positive() {
        setUpGenomes();

        assertTrue(genome1.containsProgramVariable(xVar));
        assertTrue(genome1.containsProgramVariable(yVar));
        assertTrue(genome1.containsProgramVariable(zVar));

        genome1.replaceProgramVariable(zVar.name(), yVar);

        assertTrue(genome1.containsProgramVariable(xVar));
        assertTrue(genome1.containsProgramVariable(yVar));
        assertFalse(genome1.containsProgramVariable(zVar));

    }

    @Test
    public void testReplaceVariable_negativeReplaceNonExistingVariable() {
        setUpGenomes();

        assertTrue(genomeTwoConjuncts.containsProgramVariable(xVar));
        assertTrue(genomeTwoConjuncts.containsProgramVariable(yVar));
        assertFalse(genomeTwoConjuncts.containsProgramVariable(zVar));

        genomeTwoConjuncts.replaceProgramVariable(zVar.name(), yVar);

        assertTrue(genomeTwoConjuncts.containsProgramVariable(xVar));
        assertTrue(genomeTwoConjuncts.containsProgramVariable(yVar));
        assertFalse(genomeTwoConjuncts.containsProgramVariable(zVar));
    }

}
