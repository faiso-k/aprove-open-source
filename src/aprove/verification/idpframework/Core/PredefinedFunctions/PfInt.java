/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Utility.*;

public class PfInt<R extends IntRing<R>> extends PredefinedConstructor<R> {

    private final R value;
    private final IFunctionSymbol<R> sym;
    private final IFunctionApplication<R> term;

    PfInt(final IntegerDomain<R> domain, final R value) {
        super(0, domain);
        if (Globals.useAssertions) {
            assert domain.inRange(value) : "value out of range";
        }
        this.value = value;
        this.sym = IFunctionSymbol.create(value.toString(), this);
        this.term = ITerm.createFunctionApplication(this.sym, PredefinedConstructor.EMPTY_ARGLIST);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final PfInt<?> other = (PfInt<?>) obj;
        return this.value.equals(other.value) && this.domain.equals(other.domain);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        this.value.export(sb, o, verbosityLevel);
        sb.append(DomainFactory.SUFFIX_SEPERATOR);
        this.domain.export(sb, o, verbosityLevel);
    }

    @Override
    public IDependence filterPositon(final int i) {
        throw new UnsupportedOperationException("no args");
    }

    @Override
    public IFunctionSymbol<R> getSym() {
        return this.sym;
    }

    @Override
    public IFunctionApplication<R> getTerm() {
        return this.term;
    }

    public R getValue() {
        return this.value;
    }

    @Override
    public String getName() {
        return this.value.toString();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.value == null) ? 0 : this.value.hashCode());
        return result;
    }

    @Override
    public boolean isConstructor() {
        return true;
    }

    @Override
    public ITerm<R> wrappedEvaluate(final ArrayList<? extends ITerm<?>> t, final IDPPredefinedMap predefinedMap) {
        if (t.isEmpty()) {
            return this.term;
        } else {
            return null;
        }
    }


}
