package aprove.verification.oldframework.Algebra.Terms.Visitors;
import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;

/**
 * The ContainsTermVisitor checks if a given term is a subterm of another term
 * @author Stephan Swiderski
 * @version $Id$
 */

public class ContainsTermVisitor implements CoarseGrainedTermVisitor {
    private AlgebraTerm match;
    private boolean stop;
    private Boolean result;

    /**
     * @param match the term to compare with the subterms
     */
    public ContainsTermVisitor(AlgebraTerm match){
        this.match = match;
    this.stop = false;
    this.result = Boolean.valueOf(false);
    }


    @Override
    public Object caseVariable(AlgebraVariable v) {
        if (this.match.equals(v)) {
       this.stop = true;
       this.result = Boolean.valueOf(true);
    }
    return this.result;
    }

    @Override
    public Object caseFunctionApp(AlgebraFunctionApplication f) {
        if (this.match.equals(f)) {
        this.stop = true;
            this.result = Boolean.valueOf(true);
    } else {
           //System.out.println(":");
        List<AlgebraTerm> args = f.getArguments();
        for (int i=0;i<args.size();i++){
        args.get(i).apply(this);
            if (this.stop) {
            return this.result;
        }
        }
    }
    return this.result;
    }


}
