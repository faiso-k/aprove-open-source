/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class PfInt extends PredefinedConstructor {

    private final BigIntImmutable value;
    private final FunctionSymbol sym;
    private final TRSFunctionApplication term;

    public PfInt(IntegerDomain domain, BigIntImmutable value) {
        super(0, domain);
        if (Globals.useAssertions) {
            assert domain.inRange(value.getBigInt()) : "value out of range";
        }
        this.value = value;
        this.sym = FunctionSymbol.create(value.toString(), 0);
        this.term = TRSTerm.createFunctionApplication(this.sym, ImmutableCreator.create(new ArrayList<TRSTerm>()));
    }

    @Override
    public TRSFunctionApplication getTerm() {
        return this.term;
    }

    @Override
    public TRSTerm wrappedEvaluate(List<? extends TRSTerm> t) {
        return null;
    }

    @Override
    public boolean isConstructor() {
        return true;
    }

    @Override
    public IDependence filterPositon(int i) {
        throw new UnsupportedOperationException("no args");
    }

    @Override
    public String toString() {
        return this.sym.toString();
    }

    @Override
    public FunctionSymbol getSym() {
        return this.sym;
    }

    public BigIntImmutable getValue() {
        return this.value;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.value == null) ? 0 : this.value.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        PfInt other = (PfInt) obj;
        return this.value.equals(other.value) && this.domain.equals(other.domain);
    }

    @Override
    public String export(Export_Util o) {
        return this.value.export(o) + DomainFactory.SUFFIX_SEPERATOR + this.domain.export(o);
    }


}

