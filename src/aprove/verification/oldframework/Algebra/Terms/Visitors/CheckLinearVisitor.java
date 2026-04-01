package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/** tests if a term is linear
 * @author Stephan Swiderski
 * @version $Id$
 */
public class CheckLinearVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected Collection<AlgebraVariable> vars;
    protected boolean linear;

    @Override
    public void inVariable(AlgebraVariable v) {
        if (!this.linear) {
            return ;
        }
        if (this.vars.contains(v)) { this.linear = false; }
    this.vars.add(v);

    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        if (!this.linear) {
            return null;
        }
    return super.caseFunctionApp(f);
    }

    protected CheckLinearVisitor() {
        this.vars = new LinkedHashSet<AlgebraVariable>();
    this.linear = true;
    }

    public static boolean apply(AlgebraTerm t) {
        CheckLinearVisitor clv = new CheckLinearVisitor();
        t.apply(clv);
        return clv.linear;
    }
}
