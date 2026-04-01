package aprove.verification.dpframework.TRSProblem.Utility;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * this class just provides a static method to apply a Context-Substitution to a Term
 *
 * @author Sebastian Weise
 */

public class ContextSubstitution {

    public static TRSTerm apply(TRSTerm t, final Context C, final TRSSubstitution subst,
            int n) {

        while (n > 0) {
            t = C.replace(t.applySubstitution(subst));

            n--;
        }

        return t;
    }
}
