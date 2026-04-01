package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/** Replace a term at a speicifc position.
 *  <p>
 *  Note: This visitor is pretty destructive. Copy as appropriate
 *  before use.
 * @author Eugen Yu, Peter Schneider-Kamp
 * @version $Id$
 */

public class ReplaceSubtermVisitor implements CoarseGrainedTermVisitor {

    AlgebraTerm newSubterm;
    Position p;
    Iterator i;
    int curpos;

    protected ReplaceSubtermVisitor(Position p, AlgebraTerm newSubterm) {
        this.p = p;
        this.i = p.iterator();
        this.newSubterm = newSubterm;
    }

    protected AlgebraTerm iterate(AlgebraTerm t) {
        if (!this.i.hasNext()) {
            return this.newSubterm;
        }
        this.curpos = ((Integer)this.i.next()).intValue();
        return (AlgebraTerm)t.apply(this);
    }

    //apply methods

    /** Return a term where the term at position p is replaced by
     *  newSubterm.
     */
    public static AlgebraTerm apply(AlgebraTerm t, AlgebraTerm newSubterm, Position p) {
        ReplaceSubtermVisitor v = new ReplaceSubtermVisitor(p, newSubterm);
        return (AlgebraTerm)v.iterate(t);
    }

    /** Replace the i-th direct subterm with newSubterm..
     */
    public static AlgebraTerm apply(AlgebraTerm t, AlgebraTerm newSubterm, int i) {
        Position p = Position.create();
        p.add(i);
        return ReplaceSubtermVisitor.apply(t, newSubterm, p);
    }

    //two cases:

    @Override
    public Object caseVariable(AlgebraVariable v) {
        throw new RuntimeException("Variable has no positions");
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym = f.getFunctionSymbol();
        List<AlgebraTerm> args = f.getArguments();
        try {
            AlgebraTerm t = (AlgebraTerm)args.get(this.curpos);
            args.set(this.curpos, this.iterate(t));
            return f;
        } catch (ArrayIndexOutOfBoundsException e) {
            throw new RuntimeException("Position not allowed. "+fsym.getName() + " has arity " + fsym.getArity());
        }
    }

}
