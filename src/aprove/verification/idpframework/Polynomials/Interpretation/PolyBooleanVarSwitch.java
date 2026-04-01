package aprove.verification.idpframework.Polynomials.Interpretation;

import aprove.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;

/**
 * @author MP
 */
public class PolyBooleanVarSwitch<C extends SemiRing<C>> {

    private final ItpfFactory itpfFactory;
    private final PolyFactory factory;
    private final ItpfBoolPolyVar<C> polyVariable;

    private volatile C value;
    private volatile Polynomial<C> polynomial;

    public PolyBooleanVarSwitch(final PolyFactory factory,
            final ItpfBoolPolyVar<C> polyVariable, final C value) {
        this.factory = factory;
        this.polyVariable = polyVariable;
        this.itpfFactory = polyVariable.getFactory();
        this.setValue(value);
    }

    public ItpfBoolPolyVar<C> getPolyVariable() {
        return this.polyVariable;
    }

    public synchronized void setValue(final C value) {
        if (Globals.useAssertions) {
            assert value == null || value.isOne() || value.isZero() : "illegal value" + value;
        }
        if (this.value != null) {
            throw new IllegalStateException("value already set");
        }

        this.value = value;

        if (value == null) {
            this.polynomial = this.factory.create(this.polyVariable.getPolyVar());
        } else {
            this.polynomial = this.factory.create(value);
        }
    }

    public synchronized C getValue() {
        return this.value;
    }

    public synchronized Polynomial<C> getPolynomial() {
        return this.polynomial;
    }

    public synchronized Itpf getFormula() {
        if (this.value == null) {
            return this.itpfFactory.create(this.itpfFactory.createClause(this.polyVariable, true, ITerm.EMPTY_SET));
        } else {
            if (this.value.isOne()) {
                return this.itpfFactory.createTrue();
            } else {
                return this.itpfFactory.createFalse();
            }
        }
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + this.factory.hashCode();
        result = prime * result + this.polyVariable.hashCode();
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (!(obj instanceof PolyBooleanVarSwitch)) {
            return false;
        }
        final PolyBooleanVarSwitch<?> other = (PolyBooleanVarSwitch<?>) obj;
        return this.factory.equals(other.factory)
            && this.polyVariable.equals(other.polyVariable);
    }

    @Override
    public PolyBooleanVarSwitch<C> clone() {
        return new PolyBooleanVarSwitch<C>(this.factory, this.polyVariable, this.value);
    }
}
