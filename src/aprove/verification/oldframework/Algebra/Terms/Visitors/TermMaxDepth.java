package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;


/**
* This class calculates the maximum depth of a term.
* E.g. val[x] = 1
* E.g. val[plus(x,y)] = 2
* E.g. val[plus(plus(x,0),0] = 3
*@author Eugen
*/

public class TermMaxDepth implements CoarseGrainedTermVisitor{

    @Override
    public Object caseVariable(AlgebraVariable v){
        return Integer.valueOf(1);
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f){

        int maxD = 0;
        for (Iterator i = f.getArguments().iterator(); i.hasNext();){
            AlgebraTerm t = (AlgebraTerm)i.next();
            int currD = ((Integer)t.apply(this)).intValue();
            if (currD>maxD) {
                maxD = currD;
            }
        }
        return Integer.valueOf(maxD + 1);
    }

    public static int getVal(AlgebraTerm t){
        TermMaxDepth vis = new TermMaxDepth();
        return ((Integer)t.apply(vis)).intValue();
    }

}
