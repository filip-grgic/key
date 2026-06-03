package de.uka.ilkd.key.util.loop_inv_generation.inductive_generation.structure;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import org.key_project.logic.Term;

public class DoubleBoundConjunct extends Conjunct{

    private BoundConjunct boundConjunct1;
    private BoundConjunct boundConjunct2;

    public DoubleBoundConjunct(BoundConjunct boundConjunct1, BoundConjunct boundConjunct2, Services services) {
        this(boundConjunct1, boundConjunct2, services, false);
    }

    public DoubleBoundConjunct(BoundConjunct boundConjunct1, BoundConjunct boundConjunct2, Services services, boolean negateScope) {
        super(services);
        this.boundConjunct1 = boundConjunct1;
        if (negateScope) {
            this.boundConjunct1 = this.boundConjunct1.negateScope().flipQuantifiers();
        }

        this.boundConjunct2 = boundConjunct2;
        if (negateScope) {
            this.boundConjunct2 = this.boundConjunct2.negateScope().flipQuantifiers();
        }
    }

    @Override
    public Term translateToTerm() {
        TermBuilder tb = services.getTermBuilder();
        return tb.and((JTerm) boundConjunct1.translateToTerm(), (JTerm) boundConjunct2.translateToTerm());
    }

    @Override
    public Conjunct replace(Term oldTerm, Term newTerm) {
        return new DoubleBoundConjunct(
                (BoundConjunct) boundConjunct1.replace(oldTerm, newTerm),
                (BoundConjunct) boundConjunct2.replace(oldTerm, newTerm),
                services
        );
    }

    @Override
    public String toString() {
        return boundConjunct1 + "|" + boundConjunct2;
    }

    @Override
    public boolean equals(Object o) {
        return boundConjunct1.equals(o) && boundConjunct2.equals(o);
    }

    @Override
    public int hashCode() {
        return 17 +
                29 * boundConjunct1.hashCode() +
                29 * boundConjunct2.hashCode();
    }
}
