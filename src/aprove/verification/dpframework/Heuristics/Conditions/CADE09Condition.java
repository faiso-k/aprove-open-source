package aprove.verification.dpframework.Heuristics.Conditions;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;

/**
 * CADE09Condition.<p>
 * Its check returns <code>true</code> iff P has at most <code>size</code>
 * elements and the QDPTheoremProverProcessor is applicable.<p>
 *
 * Created: April 27, 2009
 *
 * @author Carsten Fuhs
 */
public class CADE09Condition extends AbstractQDPCondition {

    // max number of elements in P
    private int size;
    private int tupleArity;

    @ParamsViaArgumentObject
    public CADE09Condition(Arguments arguments) {
        this.size = arguments.size;
        this.tupleArity = arguments.tupleArity;
    }

    @Override
    public boolean checkQDP(QDPProblem qdp, Abortion aborter) {
        boolean result = qdp.getP().size() <= this.size &&
            QDPTheoremProverProcessor.isThmProverApplicable(qdp) && (this.maxTupleArity(qdp.getP()) <= this.tupleArity);
        //System.err.println("CADE09 says: " + result);
        return result;
    }

    private int maxTupleArity(Set<Rule> P) {
        int maxArity = 0;
        for (Rule dp : P) {
            int arity = dp.getRootSymbol().getArity();
            if (arity > maxArity) {
                maxArity = arity;
            }
        }
        return maxArity;
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

    public static class Arguments {
        public int size = 6;
        public int tupleArity = Integer.MAX_VALUE;
    }
}
