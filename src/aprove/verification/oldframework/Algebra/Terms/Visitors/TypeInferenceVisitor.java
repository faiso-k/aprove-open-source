package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;

/** Returns all variables contained in a Term.
 *  <p>
 *  Note: Changing the variables will change the term's variables.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class TypeInferenceVisitor extends CoarseGrainedDepthFirstTermVisitor {

    Program.SortMap sorted;
    Object rule;

    @Override
    public void inFunctionApp(AlgebraFunctionApplication fapp) {
        List<AlgebraTerm> args = fapp.getArguments();
        for (int i = 0; i < args.size(); i++) {
            this.sorted.update(fapp, i, (AlgebraTerm)args.get(i), this.rule);
        }
    }

    protected TypeInferenceVisitor(Program.SortMap sorted, Object rule) {
        this.sorted = sorted;
        this.rule = rule;
    }

    public static void apply(AlgebraTerm t, Program.SortMap sorted, Object rule) {
        t.apply(new TypeInferenceVisitor(sorted, rule));
    }

}
