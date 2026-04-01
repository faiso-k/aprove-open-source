/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public interface IECap {


    public static enum Estimation {
        ICAP;

        public static Estimation DEFAULT = ICAP;

        public static Estimation getDefaultEstimation() {
            return ICAP;
        }

        public static IECap getEstimation(Estimation estimation) {
            if (estimation == null) {
                estimation = Estimation.DEFAULT;
            }
            if (estimation == ICAP || estimation == null) {
                return new ICap();
            }
            return null;
        }

    }

    /**
     * @author mpluecke
     *
     */
    public static interface ICapFreshNameGenerator {

        /**
         * @return fresh variable in SECOND_STANDARD_PREFIX
         */
        public TRSVariable getNextFreshVariable();
    }

    /**
     * Don't use in concurrent environment, not synchronized
     * @author mpluecke
     *
     */
    public static class CapFreshNameGenerator implements ICapFreshNameGenerator {

        int nextVarNr = 0;

        public CapFreshNameGenerator() {
        }

        public CapFreshNameGenerator(Collection<? extends TRSVariable> used) {
            for (TRSVariable var : used) {
                if (var.getName().startsWith(TRSTerm.SECOND_STANDARD_PREFIX)) {
                    try {
                        this.nextVarNr = Math.max(this.nextVarNr, Integer.parseInt(var.getName().substring(TRSTerm.SECOND_STANDARD_PREFIX.length())) + 1);
                    } catch (NumberFormatException e) {
                        // we do not need to consider var
                    }
                }
            }
        }

        @Override
        public TRSVariable getNextFreshVariable() {
            return TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX  + (this.nextVarNr++));
        }

    }


    /**
     * Computes an estimated cap function eCap. Returns t if eCap(t) = t (same object).
     * The variables introduces by eCap are taken from the given fresh name generator.
     * @param ruleAnalysis - contains R and Q
     * @param s
     * @param t - the term to be capped
     * @param freshNameGen - a generator for fresh names
     * @param useCache - may cap use cached results? WARNING: no fresh names!
     * @param fillRules - true iff result.y should be filled with rules (higher complexity)
     * @return a pair where x = capped term where all variables are from SECOND/THIRD_STANDARD_PREFIX,
     *                      y = map of topmost independent positions where rewriting steps in t with given non-pre-defined rules can be performed
     */
    public Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> cap(IDPRuleAnalysis ruleAnalysis, Set<? extends TRSTerm> s, TRSTerm t, IECap.ICapFreshNameGenerator freshNameGen, boolean useCache, boolean fillRules);

    public String getDescription();

    public Estimation getEstimation();
}
