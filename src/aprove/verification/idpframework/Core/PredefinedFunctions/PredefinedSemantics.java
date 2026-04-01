/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 * Base class for predefined functions.
 * <p>
 * There should be one non-abstract {@link PredefinedSemantics} subclass for
 * every predefined function. These classes can evaluate integer constant
 * parameters like the according predefined function would do.
 * </p>
 */
public abstract class PredefinedSemantics<R extends SemiRing<R>> extends IDPExportable.IDPExportableSkeleton implements Immutable, IDPExportable {

    public static final String DOMAIN_SEPERATOR = "@";

    /**
     * Arity of the predefined function
     */
    protected final int arity;

    /**
     * Must be called to set the arity of the function
     */
    protected PredefinedSemantics(final int arity) {
        this.arity = arity;
    }

    /**
     * Evaluates function symbol for constant parameters.
     * <p>
     * If args only consists of constants, a {@link PredefinedSemantics}
     * subclass checks if it is applicable and evaluates FUNCTION(args), where
     * FUNCTION is the function represented by the subclass.
     * @return value or null
     */
    public final ITerm<R> evaluate(final ImmutableArrayList<? extends ITerm<?>> args, final IDPPredefinedMap predefinedMap) {
        if (Globals.useAssertions) {
            assert (args.size() == this.arity);
        }

        final ITerm<R> res = this.wrappedEvaluate(args, predefinedMap);
        return res;
    }

    public abstract IDependence filterPositon(int i);

    public int getArity() {
        return this.arity;
    }

    public abstract boolean isConstructor();

    public abstract SemiRingDomain<R> getResultDomain();

    public abstract ImmutableList<? extends SemiRingDomain<?>> getDomains();

    /**
     * Implements the evaluation described at <code>evaluate</code>.
     * <p>
     * If the predefined function is not applicable, return null so the
     * unevaluated expression is returned to the user.
     * </p>
     * <p>
     * E.g. <code>+@z(3@z, 2@z)</code> evaluates to <code>5@z</code>, whereas
     * <code>+@z(3@1, 2@z)</code> evaluates to itself.
     * </p>
     * @param predefinedMap TODO
     * @return value or null
     */
    protected abstract ITerm<R> wrappedEvaluate(ArrayList<? extends ITerm<?>> t, IDPPredefinedMap predefinedMap);

}
