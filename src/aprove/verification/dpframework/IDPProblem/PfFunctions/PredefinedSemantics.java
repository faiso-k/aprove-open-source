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
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.usableRules.IActiveCondition.*;
import immutables.*;

/**
 * Base class for predefined functions.
 *
 * <p>There should be one non-abstract {@link PredefinedSemantics} subclass
 * for every predefined function. These classes can evaluate integer constant
 * parameters like the according predefined function would do.</p>
 */
public abstract class PredefinedSemantics implements Immutable, Exportable {

    public static final String DOMAIN_SEPERATOR = "@";


    /**
     * Arity of the predefined function
     */
    protected final int arity;

    /**
     * Must be called to set the arity of the function
     */
    protected PredefinedSemantics(int arity) {
        this.arity = arity;
    }

    /**
     * Evaluates function symbol for constant parameters.
     *
     * <p>If args only consists of constants, a {@link PredefinedSemantics}
     * subclass checks if it is applicable and evaluates FUNCTION(args),
     * where FUNCTION is the function represented by the subclass.
     * @return value or null
     */
    public final TRSTerm evaluate(ImmutableList<? extends TRSTerm> args) {
        if (Globals.useAssertions) {
            assert(args.size() == this.arity);
        }
        TRSTerm res =  this.wrappedEvaluate(args);
        return res;
    }

    /**
     * Implements the evaluation described at <code>evaluate</code>.
     *
     * <p>If the predefined function is not applicable, return null so the
     * unevaluated expression is returned to the user.</p>
     *
     * <p>E.g. <code>+@z(3@z, 2@z)</code> evaluates to <code>5@z</code>,
     * whereas <code>+@z(3@1, 2@z)</code> evaluates to itself.</p>
     * @return value or null
     */
    protected abstract TRSTerm wrappedEvaluate(List<? extends TRSTerm> t);

    public abstract boolean isConstructor();

    public abstract boolean isFunction();

    public int getArity() {
        return this.arity;
    }

    public abstract IDependence filterPositon(int i);



}
