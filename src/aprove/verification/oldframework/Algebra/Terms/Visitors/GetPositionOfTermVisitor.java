package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Gets a certain subterm of a term.
 * @author Burak Emir
 * @version $Id$
 */

public class GetPositionOfTermVisitor implements CoarseGrainedTermVisitor {

    Position p;
    Iterator i;
    int curpos;

    protected GetPositionOfTermVisitor( Position p ) {
    this.p = p;
    this.i = p.iterator();
    }

    protected AlgebraTerm iterate(AlgebraTerm t) {
        if (!this.i.hasNext()) {
            return t;
        }
    this.curpos = ((Integer)this.i.next()).intValue();
    return (AlgebraTerm)t.apply(this);
    }

    /** Return term at the given position.
     */
    public static AlgebraTerm apply(AlgebraTerm t, Position p) {
    GetPositionOfTermVisitor v = new GetPositionOfTermVisitor(p);
    AlgebraTerm result = v.iterate(t);
    return result;
    }

    /** Return a direct subterm of this term.
     */
    public static AlgebraTerm apply(AlgebraTerm t, int i) {
        Position p = Position.create();
        p.add(i);
    return GetPositionOfTermVisitor.apply(t, p);
    }

    @Override
    public Object caseVariable(AlgebraVariable v) {
    throw new RuntimeException("Variable has no positions");
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)f.getSymbol();
        List<AlgebraTerm> args = f.getArguments();
        try {
            AlgebraTerm t = (AlgebraTerm)args.get(this.curpos);
            return this.iterate(t);
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new RuntimeException("Position not allowed. "+fsym.getName() + " has arity " + fsym.getArity());
        }
    }

}
