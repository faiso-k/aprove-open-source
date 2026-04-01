package aprove.verification.oldframework.Algebra.Terms.Visitors;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 * Computes the length of a term, i.e. the number of function symbols
 * and variables.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class LengthVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected int length;

    @Override
    public void inVariable(AlgebraVariable v) {
        this.length++;
    }

    @Override
    public void inFunctionApp(AlgebraFunctionApplication f) {
        this.length++;
    }

    public LengthVisitor() {
        this.length = 0;
    }

    public static int apply(AlgebraTerm t) {
        LengthVisitor v = new LengthVisitor();
        t.apply(v);
        return v.length;
    }
}
