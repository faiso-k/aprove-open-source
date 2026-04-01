package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Returns all variables contained in a Term.
 *  <p>
 *  Note: Changing the variables will change the term's variables.
 * @author Burak Emir, Peter Schneider-Kamp
 * @version $Id$
 */
public class GetVariablesVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected Collection<AlgebraVariable> vars;

    @Override
    public void inVariable(AlgebraVariable v) {
        this.vars.add(v);
    }

    protected GetVariablesVisitor(boolean isSet) {
        if (isSet) {
            this.vars = new LinkedHashSet<AlgebraVariable>();
        } else {
            this.vars = new Vector<AlgebraVariable>();
        }
    }

    public static Collection<AlgebraVariable> apply(AlgebraTerm t, boolean isSet) {
        GetVariablesVisitor v = new GetVariablesVisitor(isSet);
        t.apply(v);
        return v.vars;
    }
}
