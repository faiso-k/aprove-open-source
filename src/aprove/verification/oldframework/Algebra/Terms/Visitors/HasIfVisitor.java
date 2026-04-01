package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 *Check if a term contains the If statement
 *@author eugen
 */


public class HasIfVisitor implements CoarseGrainedTermVisitor{

    @Override
    public Object caseVariable(AlgebraVariable v){
    return Boolean.valueOf(false);
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f){
    //if (f.getFunctionSymbol().equals(Symbol.IF_SYMBOL)){
    if (f.getFunctionSymbol().getName().equals(Symbol.IF_SYMBOL)) {
        return Boolean.valueOf(true);
    }
    for (Iterator i = f.getArguments().iterator(); i.hasNext();){
        AlgebraTerm t = (AlgebraTerm)i.next();
        boolean b = ((Boolean)t.apply(this)).booleanValue();
        if (b) {
            return Boolean.valueOf(true);
        }
    }
    return Boolean.valueOf(false);
    }

    public static boolean applyTo(AlgebraTerm t){
    HasIfVisitor vis = new HasIfVisitor();
    return ((Boolean)t.apply(vis)).booleanValue();
    }

}
