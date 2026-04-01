/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Algorithms.Cap;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
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
     */
    public static interface ICapFreshNameGenerator {

        /**
         * @return fresh variable in SECOND_STANDARD_PREFIX
         */
        public <R extends SemiRing<R>> IVariable<R> getNextFreshVariable(final SemiRingDomain<R> domain);
    }

    /**
     * Don't use in concurrent environment, not synchronized
     * @author mpluecke
     */
    public static class CapFreshNameGenerator implements ICapFreshNameGenerator {

        int nextVarNr = 0;

        public CapFreshNameGenerator() {
        }

        public CapFreshNameGenerator(final Collection<? extends IVariable<?>> used) {
            for (final IVariable<?> var : used) {
                if (var.getName().startsWith(ITerm.SECOND_STANDARD_PREFIX)) {
                    try {
                        this.nextVarNr =
                            Math.max(this.nextVarNr,
                                Integer.parseInt(var.getName().substring(
                                    ITerm.SECOND_STANDARD_PREFIX.length())) + 1);
                    } catch (final NumberFormatException e) {
                        // we do not need to consider var
                    }
                }
            }
        }

        @Override
        public <R extends SemiRing<R>> IVariable<R> getNextFreshVariable(final SemiRingDomain<R> domain) {
            return ITerm.createVariable(ITerm.SECOND_STANDARD_PREFIX
                + (this.nextVarNr++), domain);
        }

    }

    /**
     * Computes an estimated cap function eCap. Returns t if eCap(t) = t (same
     * object). The variables introduces by eCap are taken from the given fresh
     * name generator.
     * @param idp The IDPProblem.
     * @param s
     * @param t - the term to be capped
     * @param freshNameGen - a generator for fresh names
     * @param useCache - may cap use cached results? WARNING: no fresh names!
     * @param fillRules - true iff result.y should be filled with rules (higher
     * complexity)
     * @return a pair where x = capped term where all variables are from
     * SECOND/THIRD_STANDARD_PREFIX, y = map of topmost independent positions
     * where rewriting steps in t with given non-pre-defined rules can be
     * performed
     */
    public <R extends SemiRing<R>> Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>> cap(RuleAnalysis<IRule> rules,
        IQTermSet q,
        Set<? extends ITerm<?>> s,
        ITerm<R> t,
        IECap.ICapFreshNameGenerator freshNameGen,
        boolean useCache,
        boolean fillRules);

    public String getDescription();

    public Estimation getEstimation();
}
