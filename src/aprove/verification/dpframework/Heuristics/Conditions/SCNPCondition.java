package aprove.verification.dpframework.Heuristics.Conditions;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * SCNPCondition.<p>
 * Its check returns <code>true</code> iff P contains a rule
 * whose right-hand side has the shape F(..., t, ..., t, ...)
 * and where t contains at least <code>numSyms</code>
 * function symbols. Such DPs are good candidates for
 * max-comparison of SCNP.
 *
 * Created: May 21, 2011.
 *
 * @author Carsten Fuhs
 */
public class SCNPCondition extends AbstractQDPCondition {

    // max number of elements in P
    private int numSyms;

    @ParamsViaArgumentObject
    public SCNPCondition(Arguments arguments) {
        this.numSyms = arguments.numSyms;
    }

    @Override
    public boolean checkQDP(QDPProblem qdp, Abortion aborter) {
        for (Rule dp : qdp.getP()) {
            TRSTerm r = dp.getRight();
            if (r.isVariable()) { // SCNP does not handle collapsing DPs
                return false;
            }
            TRSFunctionApplication rFApp = (TRSFunctionApplication) r;
            Set<TRSTerm> args = new LinkedHashSet<TRSTerm>();
            for (TRSTerm t : rFApp.getArguments()) {
                boolean newlyAdded = args.add(t);
                if (! newlyAdded) {
                    // seen t before -- is it sufficiently interesting?
                    if (!(t.isVariable()) || this.numSyms <= 0) {
                        Map<FunctionSymbol, Integer> symCount = t.getFunctionSymbolCount();
                        int sum = 0;
                        for (int i : symCount.values()) {
                            sum += i;
                        }
                        if (sum >= this.numSyms) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return true;
    }

    public static class Arguments {
        public int numSyms = 2;
    }
}
