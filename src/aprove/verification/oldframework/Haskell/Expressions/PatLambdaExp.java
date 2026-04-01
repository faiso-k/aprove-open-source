package aprove.verification.oldframework.Haskell.Expressions;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The PatLambdaExp is a special form of LambdaExp explicit for Pattern Decls
 * (see also PatLambdaExpVisitor)
 * the parser use this, later it is transfomed to a normal lambda expression
 * !no! XML-Bean
 */
public class PatLambdaExp extends LambdaExp {

    /**
     * constructor for deepcopy
     */
    public PatLambdaExp(List<HaskellPat> patterns,HaskellExp result,EntityFrame entityFrame) {
         this.patterns = patterns;
         this.result = result;
         this.entityFrame = entityFrame;
    }

    /**
     * normal constructor
     */
    public PatLambdaExp(List<HaskellPat> patterns,HaskellExp result) {
         this(patterns,result,null);
    }


    @Override
    public Object deepcopy(){
         return this.hoCopy(new PatLambdaExp(Copy.deepCol(this.patterns),Copy.deep(this.getResult()),this.entityFrame));
    }

    @Override
    public HaskellObject visit(HaskellVisitor hv){
        return hv.casePatLambdaExp((PatLambdaExp)super.visit(hv));
    }

}
