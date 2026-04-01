package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/** Returns the application of the given substitution to a term.
 * applying this vistor is safe because in caseVariable() a deepcopy is returned
 * @author Burak Emir, Peter Schneider-Kamp
 * @version $Id$
 */
public class SubstitutionVisitor implements CoarseGrainedTermVisitor {

    protected AlgebraSubstitution sub;

    public SubstitutionVisitor(AlgebraSubstitution sub) {
    this.sub = sub;
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
    AlgebraTerm t = this.sub.get(v.getVariableSymbol());
    if (t == null) {
        t = v;
    }
    return t.deepcopy();
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
    Vector<AlgebraTerm> v = new Vector<AlgebraTerm>();
    for (int i = 0; i < f.getArguments().size(); i++) {
        v.add((AlgebraTerm) f.getArgument(i).apply(this));
    }
    AlgebraTerm t = AlgebraFunctionApplication.create(f.getFunctionSymbol(), v);
    t.setAttributes(f.getAttributes());
    return t;
    }

    public static AlgebraTerm apply(AlgebraTerm t, AlgebraSubstitution s) {
    return (AlgebraTerm)t.apply(new SubstitutionVisitor(s));
    }

}
