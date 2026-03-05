package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypeImplementation;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.util.loop_inv_generation.ILoopInvariantGenerator;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.Util;
import de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.util.VerificationCondition;
import org.key_project.logic.Term;

public class LoopInvariantGenerator implements ILoopInvariantGenerator {
    private final Services services;
    private static final SolverType Z3_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("Z3"))
            .findFirst().orElse(null);
    private static final SolverType CVC5_SOLVER = SolverTypes.getSolverTypes().stream()
            .filter(it -> it.getClass().equals(SolverTypeImplementation.class)
                    && it.getName().equals("cvc5"))
            .findFirst().orElse(null);

    public LoopInvariantGenerator(Services services) {
        this.services = services;
    }

    @Override
    public Term generateLoopInvariant() {
        VerificationCondition[] verificationConditions = Util.generateVerificationConditions(CVC5_SOLVER, services);

//        LocationVariable indexVar = services.getTermBuilder().locationVariable("index_1", services.getTypeConverter().getIntegerLDT().targetSort(), false);
//        Term term = services.getTermBuilder().equals(services.getTermBuilder().var(indexVar), services.getTermBuilder().one());
        LocationVariable aVar = services.getTermBuilder().locationVariable("a", services.getTypeConverter().getIntegerLDT().targetSort(), false);
        LocationVariable bVar = services.getTermBuilder().locationVariable("b", services.getTypeConverter().getIntegerLDT().targetSort(), false);
        LocationVariable cVar = services.getTermBuilder().locationVariable("c", services.getTypeConverter().getIntegerLDT().targetSort(), false);
        LocationVariable indexVar = services.getTermBuilder().locationVariable("index_1", services.getTypeConverter().getIntegerLDT().targetSort(), false);
        JTerm term1 = services.getTermBuilder().leq(services.getTermBuilder().var(indexVar), services.getTermBuilder().var(bVar));
        JTerm mul = services.getTermBuilder().func(services.getTypeConverter().getIntegerLDT().getMul(), services.getTermBuilder().var(aVar), services.getTermBuilder().var(indexVar));
        JTerm term2 = services.getTermBuilder().equals(services.getTermBuilder().var(cVar), mul);
        Term term = services.getTermBuilder().and(term1, term2);
        System.out.println(verificationConditions[0].checkFulfillment(term1));
        System.out.println(verificationConditions[1].checkFulfillment(term1));
        System.out.println(verificationConditions[2].checkFulfillment(term1));

        return null;
    }


}
