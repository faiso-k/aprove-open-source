package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Debug.*;

/**
 * Termination result with a lexicographic ranking function.
 * @author cryingshadow
 * @version $Id$
 */
public class CooperationTerminating extends CooperationResult {

    /**
     * The ranking function.
     */
    private final Map<TRSFunctionApplication, List<SimplePolynomial>> ranking;

    /**
     * @param r The ranking function.
     */
    public CooperationTerminating(Map<TRSFunctionApplication, List<SimplePolynomial>> r) {
        this.ranking = new LinkedHashMap<TRSFunctionApplication, List<SimplePolynomial>>();
        if (r != null) {
            for (TRSFunctionApplication fSym : r.keySet()) {
                final List<SimplePolynomial> f = r.get(fSym);
                if (f != null && !f.isEmpty()) {
                    this.ranking.put(fSym, f);
                }
            }
            for (Entry<TRSFunctionApplication, List<SimplePolynomial>> entry : r.entrySet()) {
                Log.report("CoopRes", entry.toString());
            }
        }
    }

    /**
     * @return The ranking function.
     */
    public Map<TRSFunctionApplication, List<SimplePolynomial>> getRanking() {
        return this.ranking;
    }

    @Override
    public Result toResult() {
        return ResultFactory.proved(new SafetyIntTRSPoloRedPairProof(this.ranking));
    }

    @Override
    public String toString() {
        return "TERMINATING";
    }

}
