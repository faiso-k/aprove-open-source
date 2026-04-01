package aprove.verification.oldframework.Algebra.Terms.Visitors;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * Count the number of occurences of a given symbol.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class CountVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected int count;
    protected Symbol sym;

    @Override
    public void inVariable(AlgebraVariable v) {
        if (v.getSymbol().equals(this.sym)) {
            this.count++;
        }
    }

    @Override
    public void inFunctionApp(AlgebraFunctionApplication f) {
        if (f.getSymbol().equals(this.sym)) {
            this.count++;
        }
    }

    public CountVisitor(Symbol sym) {
        this.count = 0;
        this.sym = sym;
    }

    public static int apply(AlgebraTerm t, Symbol sym) {
        CountVisitor v = new CountVisitor(sym);
        t.apply(v);
        return v.count;
    }
}