package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 *Try to give an index which indicates the complexity of a term
 *@author Eugen
 */
public class TermIndex1 implements FineGrainedTermVisitor{
    /**
    * This class calculates the term complexity index
    * E.g. val[x] = 2
    * E.g. val[cons] = 1
    * E.g. val[cons(plus(x,y),x)] = 1 + val[all args]
    * E.g. val[plus(plus(x,0),0] =  2 + val[all args]
    *@author Eugen
    */

    /** the variable case
     */


    @Override
    public Object caseVariable(AlgebraVariable v){
    return Integer.valueOf(2);
    }


    @Override
    public Object caseConstructorApp( ConstructorApp cterm ){
    return Integer.valueOf(1+this.sumOfArgsVal(cterm.getArguments().iterator()));
    }

    @Override
    public Object caseDefFunctionApp( DefFunctionApp fterm ){
    return Integer.valueOf(2+ this.sumOfArgsVal(fterm.getArguments().iterator()));
    }

    //i is an iterator through a list of terms
    protected int sumOfArgsVal(Iterator i){
    int result = 0;
    for (;i.hasNext();){
        AlgebraTerm t = (AlgebraTerm)i.next();
        result = result +  ((Integer)t.apply(this)).intValue();
    }
    return result;
    }

    public static int getVal(AlgebraTerm t){
    TermIndex1 vis = new TermIndex1();
    return ((Integer)t.apply(vis)).intValue();
    }

    @Override
    public Object caseMetaFunctionApplication(MetaFunctionApplication metaFunctionApplication) {
        return null;
    }


}
