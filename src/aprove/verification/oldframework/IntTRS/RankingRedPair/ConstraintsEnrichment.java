package aprove.verification.oldframework.IntTRS.RankingRedPair;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.Ranking.*;
import aprove.verification.oldframework.IntTRS.RankingRedPair.RankingRedPairProcessor.*;

/**
 * Takes a transition relation and create a relation with an enriched constraint
 * system, which is obtained by adding following constraints.
 * @author Matthias Hoelzel
 */
public class ConstraintsEnrichment {
    /** The original relation */
    private final TransitionRelation originalRelation;

    /** Processor arguments */
    private final Arguments args;

    /** The thing that might tell us to abort. */
    private final Abortion abortion;

    /**
     * Constructor! Creates your new constraints enrichment!
     * @param toBeEnriched some PCS
     * @param arguments some processor arguments
     * @param abort the thing that might tell us to abort.
     */
    public ConstraintsEnrichment(final TransitionRelation toBeEnriched, final Arguments arguments, final Abortion abort)
    {
        assert toBeEnriched != null && arguments != null : "Null?!";
        this.originalRelation = toBeEnriched;
        this.args = arguments;
        this.abortion = abort;
    }

    /**
     * Runs the procedure and returns the enriched PCS.
     * @return some new PCS
     * @throws AbortionException thrown if we were aborted.
     */
    public TransitionRelation enrich() throws AbortionException {
        final PCS oldPCS = this.originalRelation.getPCS();
        final LinkedHashSet<GEConstraint> constraints = new LinkedHashSet<>(oldPCS.getConstraints());

        boolean changed;
        do {
            changed = false;

            testing: for (final GEConstraint firstConstraint : constraints) {
                this.abortion.checkAbortion();
                for (final GEConstraint secondConstraint : constraints) {
                    final VarPolynomial geZeroPoly;
                    if (firstConstraint.getConstant().compareTo(BigInteger.ZERO) > 0) {
                        geZeroPoly = firstConstraint.getPoly();
                    } else {
                        geZeroPoly =
                            firstConstraint.getPoly().minus(VarPolynomial.create(firstConstraint.getConstant()));
                    }

                    final VarPolynomial secondLeftMinusRight =
                        secondConstraint.getPoly().minus(VarPolynomial.create(secondConstraint.getConstant()));
                    final GEConstraint newConstraint =
                        GEConstraint.create(secondLeftMinusRight.times(geZeroPoly), BigInteger.ZERO);
                    if (!constraints.contains(newConstraint)
                        && newConstraint.getPoly().getDegree() < 3
                        && newConstraint.getPoly().getVarMonomials().size() < 6)
                    {
                        changed = true;
                        constraints.add(newConstraint);
                        break testing;
                    }
                }
            }

        } while (changed);

        final PCS newPCS = new PCS(new LinkedList<>(constraints), this.abortion);

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("enrichment");
            l.logln("OLD PCS:");
            l.logln(oldPCS);
            l.logln("NEW PCS:");
            l.logln(newPCS);
            l.logln();
        }

        return new TransitionRelation(
            newPCS,
            this.originalRelation.getStartSymbol(),
            this.originalRelation.getStartVariables(),
            this.originalRelation.getEndSymbol(),
            this.originalRelation.getEndVariables(),
            false,
            this.abortion);
    }
}
