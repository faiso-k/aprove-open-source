package aprove.verification.oldframework.Algebra.Terms.Visitors;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 * Checks if the given term contains only function symbols of arity
 * at most 1.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class CheckMaxUnaryVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected boolean unary;

    @Override
    public void inFunctionApp(AlgebraFunctionApplication fapp) {
        if (fapp.getFunctionSymbol().getArity() > 1) {
            this.unary = false;
        }
    }

    protected CheckMaxUnaryVisitor() {
        this.unary = true;
    }

    public static boolean apply(AlgebraTerm t) {
        CheckMaxUnaryVisitor v = new CheckMaxUnaryVisitor();
        t.apply(v);
        return v.unary;
    }
}
