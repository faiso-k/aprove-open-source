/**
 *
 * @author Martin Pluecker
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class PfUndefinedInt extends PredefinedConstructor {

    private final FunctionSymbol sym;
    private final TRSFunctionApplication term;

    public PfUndefinedInt(IntegerDomain domain) {
        super(0, domain);
        this.sym = FunctionSymbol.create("undefinedInt" + domain.getBits(), 0);
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

    @Override
    public int hashCode() {
        return 31;
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
        PfUndefinedInt other = (PfUndefinedInt) obj;
        return this.domain.equals(other.domain);
    }

    @Override
    public String export(Export_Util o) {
        return this.sym.export(o);
    }


}

