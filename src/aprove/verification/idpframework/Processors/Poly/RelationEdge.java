package aprove.verification.idpframework.Processors.Poly;

import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class RelationEdge<R extends SemiRing<R>> extends IDPExportable.IDPExportableSkeleton implements Immutable {

    public final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> from;

    public final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> to;
    public final R toOffset;

    private final int hashCode;

    public RelationEdge(final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> from, final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> to, final R toOffset) {
        this(from, to, toOffset, false);
    }

    public RelationEdge(final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> from, final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> to, final R toOffset, final boolean valid) {
        this.from = from;
        this.to = to;
        this.toOffset = toOffset;

        if (!valid) {
            this.validate();
        }

        final int prime = 31;
        int result = 1;
        result = prime * result + from.hashCode();
        result = prime * result + to.hashCode();
        result = prime * result + toOffset.hashCode();

        this.hashCode = result;
    }

    private void validate() {
        if (Globals.useAssertions) {
            this.validatePositivePoly(this.from);
            this.validatePositivePoly(this.to);

            // check disjoint polys
            final Set<ImmutableMap<RelationNode<R>, BigInt>> intersection = new HashSet<ImmutableMap<RelationNode<R>, BigInt>>(this.from.keySet());
            intersection.retainAll(this.to.keySet());

            assert intersection.isEmpty() : "normalize edge, e.g. x >= 2 * x must be normalized to 0 >= x";
        }
    }

    private void validatePositivePoly(final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> poly) {
        for (final Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R> monomialCoeff : poly.entrySet()) {
            assert monomialCoeff.getValue().signum() > 0;
            assert !monomialCoeff.getKey().isEmpty() : "empty exponent map not allowed - use from/toOffset";
            for (final BigInt exp : monomialCoeff.getKey().values()) {
                assert exp.signum() > 0 : "non positive exponents not allowed";
            }
        }
    }

    public RelationEdge<R> invert() {
        return new RelationEdge<R>(this.to, this.from, this.toOffset.negate(), true);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }

        final RelationEdge<?> other = (RelationEdge<?>) obj;
        return this.from.equals(other.from)
            && this.to.equals(other.to)
            && this.toOffset.equals(other.toOffset);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        this.exportPoly(this.from, this.toOffset.zero(), sb, eu, verbosityLevel);
        sb.append(" ");
        sb.append(eu.geSign());
        sb.append(" ");
        this.exportPoly(this.to, this.toOffset, sb, eu, verbosityLevel);
    }

    private void exportPoly(final ImmutableMap<ImmutableMap<RelationNode<R>, BigInt>, R> poly,
        final R offset, final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        final Iterator<Map.Entry<ImmutableMap<RelationNode<R>, BigInt>, R>> targetIterator = poly.entrySet().iterator();
        while (targetIterator.hasNext()) {
            final Entry<ImmutableMap<RelationNode<R>, BigInt>, R> targetEntry =
                targetIterator.next();
            if (!targetEntry.getValue().isOne() || targetEntry.getKey().isEmpty()) {
                targetEntry.getValue().export(sb, eu, verbosityLevel);
                if (!targetEntry.getKey().isEmpty()) {
                    sb.append(" ");
                    sb.append(eu.multSign());
                    sb.append(" ");
                }
            }

            final Iterator<Map.Entry<RelationNode<R>, BigInt>> expIterator = targetEntry.getKey().entrySet().iterator();
            while (expIterator.hasNext()) {
                final Map.Entry<RelationNode<R>, BigInt> expEntry = expIterator.next();

                expEntry.getKey().export(sb, eu, verbosityLevel);
                if (!expEntry.getValue().isOne()) {
                    sb.append(eu.sup(expEntry.getValue().export(eu, verbosityLevel)));
                }
                if (expIterator.hasNext()) {
                    sb.append(" ");
                    sb.append(eu.multSign());
                    sb.append(" ");
                }
            }

            if (targetIterator.hasNext()) {
                sb.append(" + ");
            }
        }

        if (!offset.isZero() || poly.isEmpty()) {
            if (!poly.isEmpty() || offset.signum() < 0) {
                if (offset.signum() > 0) {
                    sb.append(" + ");
                } else {
                    if (poly.isEmpty()) {
                        sb.append("- ");
                    } else {
                        sb.append(" - ");
                    }
                }
            }

            if (offset.signum() >= 0) {
                offset.export(sb, eu, verbosityLevel);
            } else {
                offset.negate().export(sb, eu, verbosityLevel);
            }
        }
    }

    public boolean isUnsat() {
        return this.toOffset.signum() > 0 && this.from.isEmpty() && this.to.isEmpty();
    }
}