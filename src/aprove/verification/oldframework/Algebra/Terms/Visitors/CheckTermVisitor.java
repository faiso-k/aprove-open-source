package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** A visitor sanity checking a term's data structure.
 * @author Burak Emir
 * @version $Id$
 */
public class CheckTermVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected HashSet<CheckTermVisitor> checked;

    protected void checkSymbol(Symbol sym) {
        if (sym == null) {
            throw new RuntimeException("symbol must not equal null");
        }
        sym.check(this.checked);
    }

    @Override
    public void inVariable(AlgebraVariable v) {
        this.checkSymbol(v.getSymbol());
        this.checked.add(this);
    }

    @Override
    public void inFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)f.getSymbol();
        List<AlgebraTerm> args = f.getArguments();
        this.checkSymbol(fsym);
        if (args==null) {
            throw new RuntimeException("args must not equal null");
        }
        if (args.size() != fsym.getArity()) {
            throw new RuntimeException("term should have "
                                       + fsym.getArity()
                                       + " parameters, but has "+
                                       args.size());
        }
        this.checked.add(this);
    }

    protected CheckTermVisitor(HashSet<CheckTermVisitor> s) {
        this.checked = s;
    }

    public static void apply(AlgebraTerm t) {
        CheckTermVisitor.apply(t, new HashSet<CheckTermVisitor>());
    }

    public static void apply(AlgebraTerm t, Set<CheckTermVisitor> s) {
        CheckTermVisitor v = new CheckTermVisitor(new HashSet<CheckTermVisitor>(s));
        s.addAll(v.checked);
    }

}
