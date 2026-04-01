package aprove.verification.idpframework.Algorithms.Cap;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;
/**
 *
 * @author MP
 */
public interface IGraphCap {

    public static enum Estimation {
        ICAP, FAST;

        public static Estimation DEFAULT = FAST;

        public static Estimation getDefaultEstimation() {
            return Estimation.DEFAULT;
        }

        public static IGraphCap getEstimation(Estimation estimation) {
            if (estimation == null) {
                estimation = Estimation.DEFAULT;
            }
            if (estimation == ICAP || estimation == null) {
                return new GraphICap();
            }
            if (estimation == FAST || estimation == null) {
                return new GraphFastCap();
            }
            throw new UnsupportedOperationException("unhandled estimation");
        }

    }

    /**
     * Computes an estimated cap function eCap. Returns t if eCap(t) = t (same
     * object). The variables introduces by eCap are taken from the given fresh
     * var generator.
     */
    public <R extends SemiRing<R>> Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IEdge>>> cap(IDependencyGraph graph,
        Set<? extends ITerm<?>> s,
        FreshVarGenerator freshVarGen,
        ITerm<R> t,
        boolean requireMatching);

    public String getDescription();

    public Estimation getEstimation();
}
