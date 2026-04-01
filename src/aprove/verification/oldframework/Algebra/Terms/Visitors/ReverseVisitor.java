package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Reverse the given term.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class ReverseVisitor extends CoarseGrainedDepthFirstTermVisitor {

    protected Sort poly;
    protected AlgebraTerm rev;
    protected FreshNameGenerator fg;

    @Override
    public void inFunctionApp(AlgebraFunctionApplication fapp) {
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(this.rev);
//        System.out.println("Looking at "+fapp);
//        System.out.println("rev before "+rev);
        SyntacticFunctionSymbol fsym = fapp.getFunctionSymbol();
        Vector<Sort> vs = new Vector<Sort>();
        vs.add(this.poly);
        fsym = ConstructorSymbol.create(this.fg.getFreshName(fsym.getName(), true), vs, this.poly);
        this.rev = AlgebraFunctionApplication.create(fsym, args);
//        System.out.println("rev after "+rev);
    }

    protected ReverseVisitor(FreshNameGenerator fg) {
        this.poly = Sort.create(Sort.standardName);
        this.rev = AlgebraVariable.create(VariableSymbol.create("x", this.poly));
        this.fg = fg;
    }

    public static AlgebraTerm apply(AlgebraTerm t, FreshNameGenerator fg) {
        ReverseVisitor v = new ReverseVisitor(fg);
        t.apply(v);
        return v.rev;
    }

}
