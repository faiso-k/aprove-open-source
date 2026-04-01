/**
 * @author Martin Pluecker
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Utility.*;

public class PfBoolean extends PredefinedConstructor<BooleanRing> {

    static final String NAME_TRUE = "TRUE";
    static final String NAME_FALSE = "FALSE";

    static final PfBoolean TRUE = new PfBoolean(true);
    static final PfBoolean FALSE = new PfBoolean(false);

    static final IFunctionSymbol<BooleanRing> FS_TRUE = PfBoolean.TRUE.getSym();
    static final IFunctionSymbol<BooleanRing> FS_FALSE = PfBoolean.FALSE.getSym();
    static final IFunctionApplication<BooleanRing> TERM_TRUE = PfBoolean.TRUE.getTerm();
    static final IFunctionApplication<BooleanRing> TERM_FALSE = PfBoolean.FALSE.getTerm();

    private final boolean value;
    private final IFunctionSymbol<BooleanRing> sym;
    private final IFunctionApplication<BooleanRing> term;

    private PfBoolean(final boolean value) {
        super(0, DomainFactory.BOOLEANS);
        this.value = value;
        this.sym = IFunctionSymbol.create(value ? PfBoolean.NAME_TRUE : PfBoolean.NAME_FALSE, this);
        this.term = ITerm.createFunctionApplication(this.sym, PredefinedConstructor.EMPTY_ARGLIST);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        if (this.value) {
            sb.append(PfBoolean.NAME_TRUE);
        } else {
            sb.append(PfBoolean.NAME_FALSE);
        }
    }

    @Override
    public IDependence filterPositon(final int i) {
        throw new UnsupportedOperationException();
    }

    @Override
    public IFunctionSymbol<BooleanRing> getSym() {
        return this.sym;
    }

    @Override
    public IFunctionApplication<BooleanRing> getTerm() {
        return this.term;
    }

    @Override
    protected ITerm<BooleanRing> wrappedEvaluate(final ArrayList<? extends ITerm<?>> t, final IDPPredefinedMap predefinedMap) {
        return this.term;
    }

    @Override
    public String getName() {
        if (this.value) {
            return PfBoolean.NAME_TRUE;
        } else {
            return PfBoolean.NAME_FALSE;
        }
    }

}
