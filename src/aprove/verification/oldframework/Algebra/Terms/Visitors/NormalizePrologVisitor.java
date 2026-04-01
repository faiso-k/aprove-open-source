package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Returns the application of the given substitution to a term.
 * applying this vistor is safe because in caseVariable() a deepcopy is returned
 * @author Burak Emir, Peter Schneider-Kamp
 * @version $Id$
 */
public class NormalizePrologVisitor implements CoarseGrainedTermVisitor {

    @Override
    public Object caseVariable(AlgebraVariable v) {
    return v.deepcopy();
    }

    private boolean is(SyntacticFunctionSymbol fsym, String name) {
        return (fsym instanceof SyntacticFunctionSymbol) && (fsym.getName().equals(name)) && (fsym.getArity() == 2); // should be PredicateSymbol
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym = f.getFunctionSymbol();
        if (this.is(fsym, ",")) {
            AlgebraTerm f1 = f.getArgument(0);
            AlgebraTerm f2 = f.getArgument(1);
            SyntacticFunctionSymbol fsym1 = f1 instanceof AlgebraFunctionApplication ? ((AlgebraFunctionApplication)f1).getFunctionSymbol() : null;
            SyntacticFunctionSymbol fsym2 = f2 instanceof AlgebraFunctionApplication ? ((AlgebraFunctionApplication)f2).getFunctionSymbol() : null;
            if (this.is(fsym1, ";")) {
                f2 = (AlgebraTerm)f2.apply(this);
                Vector<AlgebraTerm> v1 = new Vector<AlgebraTerm>();
                v1.add(((AlgebraFunctionApplication)f1).getArgument(0));
                v1.add(f2);
                AlgebraTerm t1 = AlgebraFunctionApplication.create(fsym, v1);
                Vector<AlgebraTerm> v2 = new Vector<AlgebraTerm>();
                v1.add(((AlgebraFunctionApplication)f1).getArgument(1));
                v1.add(f2);
                AlgebraTerm t2 = AlgebraFunctionApplication.create(fsym, v1);
                Vector<AlgebraTerm> v = new Vector<AlgebraTerm>();
                v.add((AlgebraTerm) t1.apply(this));
                v.add((AlgebraTerm) t2.apply(this));
                AlgebraTerm t = AlgebraFunctionApplication.create(fsym1, v);
                return t;
            } else if (this.is(fsym2, ";")) {
                f1 = (AlgebraTerm)f1.apply(this);
                Vector<AlgebraTerm> v1 = new Vector<AlgebraTerm>();
                v1.add(f1);
                v1.add(((AlgebraFunctionApplication)f2).getArgument(0));
                AlgebraTerm t1 = AlgebraFunctionApplication.create(fsym, v1);
                Vector<AlgebraTerm> v2 = new Vector<AlgebraTerm>();
                v2.add(f1);
                v2.add(((AlgebraFunctionApplication)f2).getArgument(1));
                AlgebraTerm t2 = AlgebraFunctionApplication.create(fsym, v2);
                Vector<AlgebraTerm> v = new Vector<AlgebraTerm>();
                v.add((AlgebraTerm) t1.apply(this));
                v.add((AlgebraTerm) t2.apply(this));
                AlgebraTerm t = AlgebraFunctionApplication.create(fsym1, v);
                return t;
            }
        }
    Vector<AlgebraTerm> v = new Vector<AlgebraTerm>();
    for (int i = 0; i < f.getArguments().size(); i++) {
        v.add((AlgebraTerm) f.getArgument(i).apply(this));
    }
    AlgebraTerm t = AlgebraFunctionApplication.create(fsym, v);
    t.setAttributes(f.getAttributes());
    return t;
    }

    public static AlgebraTerm apply(AlgebraTerm t) {
    return (AlgebraTerm)t.apply(new NormalizePrologVisitor());
    }

}
