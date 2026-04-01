/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.IDPProblem.utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Applies constant folding to a {@link TRSTerm} (or a {@link Rule}, ...).
 *
 * <p>
 * his class makes use of the PfFunctions package and recursively evaluates
 * all integer expressions having only (after evaluation of the parameters)
 * constant integer parameters.
 * </p>
 *
 * @author noschinski
 *
 */
public class ConstantFolding {

    /**
     * Applies constant folding to a {@link TRSTerm}.
     */
    public static TRSTerm fold(TRSTerm t, IDPPredefinedMap predefinedMap) {
        if (t.isVariable()) {
            return t;
        }

        TRSFunctionApplication fa = (TRSFunctionApplication)t;
        FunctionSymbol rootSym = fa.getRootSymbol();
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(rootSym.getArity());

        for (TRSTerm arg : fa.getArguments()) {
            newArgs.add(ConstantFolding.fold(arg, predefinedMap));
        }

        ImmutableArrayList<TRSTerm> imArgs = ImmutableCreator.create(newArgs);


        PredefinedSemantics fn = predefinedMap.getPredefinedSemantics(rootSym);
        if (fn != null) {
            TRSTerm value = fn.evaluate(imArgs);
            if (value != null) {
                return value;
            }
        }
        return TRSTerm.createFunctionApplication(rootSym, imArgs);

    }

    /**
     * Applies constant folding to the rhs of a {@link Rule}
     */
    public static GeneralizedRule fold(GeneralizedRule r, IDPPredefinedMap predefinedMap) {
        return GeneralizedRule.create(r.getLeft(), ConstantFolding.fold(r.getRight(), predefinedMap));
    }
}
