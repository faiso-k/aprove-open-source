/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.oldframework.BasicStructures.*;

public class PfBoolean extends PredefinedConstructor {

    static PfBoolean TRUE = new PfBoolean(true);
    static PfBoolean FALSE = new PfBoolean(false);

    static final String NAME_TRUE = "TRUE";
    static final String NAME_FALSE = "FALSE";
    static final FunctionSymbol FS_TRUE = FunctionSymbol.create(PfBoolean.NAME_TRUE, 0);
    static final FunctionSymbol FS_FALSE = FunctionSymbol.create(PfBoolean.NAME_FALSE, 0);
    static final TRSFunctionApplication TERM_TRUE = TRSFunctionApplication.createFunctionApplication(PfBoolean.FS_TRUE);
    static final TRSFunctionApplication TERM_FALSE = TRSFunctionApplication.createFunctionApplication(PfBoolean.FS_FALSE);

    private final boolean value;

    private PfBoolean(boolean value) {
        super(0, DomainFactory.BOOLEAN);
        this.value = value;
    }

    @Override
    public FunctionSymbol getSym() {
        return this.value ? PfBoolean.FS_TRUE : PfBoolean.FS_FALSE;
    }

    @Override
    protected TRSTerm wrappedEvaluate(List<? extends TRSTerm> t) {
        return this.value ? PfBoolean.TERM_TRUE : PfBoolean.TERM_FALSE;
    }

    @Override
    public IDependence filterPositon(int i) {
        throw new UnsupportedOperationException();
    }

    @Override
    public TRSFunctionApplication getTerm() {
        return this.value ? PfBoolean.TERM_TRUE : PfBoolean.TERM_FALSE;
    }

    @Override
    public String export(Export_Util o) {
        return this.value ? "TRUE" : "FALSE";
    }

}
