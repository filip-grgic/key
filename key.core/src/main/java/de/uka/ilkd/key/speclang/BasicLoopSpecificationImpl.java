package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.Visitor;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.util.InfFlowSpec;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.HashMap;
import java.util.Map;
import java.util.function.UnaryOperator;


/**
 * A loop invariant, consisting of an invariant formula, a set of loop
 * predicates, a modifies clause, and a variant term.
 */
public class BasicLoopSpecificationImpl implements LoopSpecification {

    private final LoopStatement loop;
    private final JTerm loopInv;
    private final JTerm modifiable;

    public BasicLoopSpecificationImpl(LoopStatement loop, JTerm loopInv, JTerm modifiable) {
        this.loop = loop;
        this.loopInv = loopInv;
        this.modifiable = modifiable;
    }

    @Override
    public LoopSpecification map(UnaryOperator<JTerm> op, Services services) {
        return null;
    }

    @Override
    public LoopStatement getLoop() {
        return this.loop;
    }

    @Override
    public IProgramMethod getTarget() {//return exception
        return null;
    }

    @Override
    public JTerm getInvariant(LocationVariable heap, JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services) {
        return loopInv;
    }

    @Override
    public JTerm getInvariant(Services services) {
        return this.loopInv;
    }

    @Override
    public JTerm getFreeInvariant(LocationVariable heap, JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services) {
        return null;
    }

    @Override
    public JTerm getFreeInvariant(Services services) {
        return null;
    }

    @Override
    public JTerm getModifiable(LocationVariable heap, JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services) {
        return modifiable;
    }

    @Override
    public JTerm getModifiable(JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services) {
        return modifiable;
    }

    @Override
    public JTerm getFreeModifiable(LocationVariable heap, JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services) {
        return modifiable;
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap) {
        return ImmutableSLList.<InfFlowSpec>nil();
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(Services services) {
        return ImmutableSLList.<InfFlowSpec>nil();
    }

    @Override
    public ImmutableList<InfFlowSpec> getInfFlowSpecs(LocationVariable heap, JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services) {
        return ImmutableSLList.<InfFlowSpec>nil();
    }

    @Override
    public boolean hasInfFlowSpec(Services services) {
        return false;
    }

    @Override
    public JTerm getVariant(JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services) {
        return null;
    }

    @Override
    public JTerm getInternalSelfTerm() {
        return null;
    }

    @Override
    public JTerm getModifiable() {
        return modifiable;
    }

    @Override
    public Map<LocationVariable, JTerm> getInternalAtPres() {
        return new HashMap<>();
    }

    @Override
    public Map<LocationVariable, JTerm> getInternalInvariants() {
        return new HashMap<>();
    }

    @Override
    public Map<LocationVariable, JTerm> getInternalFreeInvariants() {
        return new HashMap<>();
    }

    @Override
    public JTerm getInternalVariant() {
        return null;
    }

    @Override
    public Map<LocationVariable, JTerm> getInternalModifiable() {
        return new HashMap<>();
    }

    @Override
    public Map<LocationVariable, JTerm> getInternalFreeModifiable() {
        return Map.of();
    }

    @Override
    public Map<LocationVariable, ImmutableList<InfFlowSpec>> getInternalInfFlowSpec() {
        return new HashMap<>();
    }

    @Override
    public LoopSpecification create(LoopStatement loop, IProgramMethod pm, KeYJavaType kjt,
                                    Map<LocationVariable, JTerm> invariants, Map<LocationVariable, JTerm> freeInvariants,
                                    Map<LocationVariable, JTerm> modifiable, Map<LocationVariable, JTerm> freeModifiable,
                                    Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, JTerm variant,
                                    JTerm selfTerm, ImmutableList<JTerm> localIns, ImmutableList<JTerm> localOuts,
                                    Map<LocationVariable, JTerm> atPres) {
        return this;
    }

    @Override
    public LoopSpecification create(LoopStatement loop,
                                    Map<LocationVariable, JTerm> invariants, Map<LocationVariable, JTerm> freeInvariants,
                                    Map<LocationVariable, JTerm> modifiable, Map<LocationVariable, JTerm> freeModifiable,
                                    Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, JTerm variant,
                                    JTerm selfTerm, ImmutableList<JTerm> localIns, ImmutableList<JTerm> localOuts,
                                    Map<LocationVariable, JTerm> atPres) {
        return this;
    }

    @Override
    public LoopSpecification instantiate(Map<LocationVariable, JTerm> invariants, Map<LocationVariable, JTerm> freeInvariants, JTerm variant) {
        return this;
    }

    @Override
    public LoopSpecification configurate(
            Map<LocationVariable, JTerm> invariants, Map<LocationVariable, JTerm> freeInvariants,
            Map<LocationVariable, JTerm> modifiable, Map<LocationVariable, JTerm> freeModifiable,
            Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs, JTerm variant) {
        return this;
    }

    @Override
    public LoopSpecification setLoop(LoopStatement loop) {
        return this;
    }

    @Override
    public LoopSpecification setTarget(IProgramMethod newPM) {
        return this;
    }

    @Override
    public LoopSpecification setInvariant(Map<LocationVariable, JTerm> invariants, Map<LocationVariable, JTerm> freeInvariants, JTerm selfTerm, Map<LocationVariable, JTerm> atPres, Services services) {
        return this;
    }

    @Override
    public void visit(Visitor v) {

    }

    @Override
    public String getPlainText(Services services, Iterable<LocationVariable> heapContext, boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        return loopInv.toString();
    }

    @Override
    public String getUniqueName() {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }

    @Override
    public String getDisplayName() {
        return null;
    }

    @Override
    public VisibilityModifier getVisibility() {
        return null;
    }

    @Override
    public KeYJavaType getKJT() {
        return null;
    }

    @Override
    public LoopSpecification setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return null;
    }

    @Override
    public Contract.OriginalVariables getOrigVars() {
        return null;
    }
}