package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import immutables.*;

public class LocalSizeBound implements Exportable {
    private final ImmutableLinkedHashSet<Integer> A;
    private final LocalComplexityValue c;
    private final CallArgument alpha;

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.A == null) ? 0 : this.A.hashCode());
        result = prime * result + ((this.alpha == null) ? 0 : this.alpha.hashCode());
        result = prime * result + ((this.c == null) ? 0 : this.c.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        LocalSizeBound other = (LocalSizeBound) obj;
        if (this.A == null) {
            if (other.A != null) {
                return false;
            }
        } else if (!this.A.equals(other.A)) {
            return false;
        }
        if (this.alpha == null) {
            if (other.alpha != null) {
                return false;
            }
        } else if (!this.alpha.equals(other.alpha)) {
            return false;
        }
        if (this.c == null) {
            if (other.c != null) {
                return false;
            }
        } else if (!this.c.equals(other.c)) {
            return false;
        }
        return true;
    }

    public LocalSizeBound(ImmutableLinkedHashSet<Integer> A, LocalComplexityValue c, CallArgument alpha) {
        this.A = A;
        this.c = c;
        this.alpha = alpha;

        if (Globals.useAssertions) {
            CpxIntTupleRule rule = alpha.rule;
            TRSFunctionApplication lhs = rule.getLeft();
            int arity = lhs.getArguments().size();
            for (int i : A) {
                assert i >= 0 && i < arity;
            }
        }
    }

    public ImmutableLinkedHashSet<Integer> getA() {
        return this.A;
    }

    public LocalComplexityValue getC() {
        return this.c;
    }

    public CallArgument getAlpha() {
        return this.alpha;
    }

    @Override
    public String export(Export_Util eu) {
        LinkedHashMap<Position, IDPExport.PositionMarker> lhsMarkers = new LinkedHashMap<>();
        for (int i : this.A) {
            lhsMarkers.put(Position.create(i), IDPExport.PositionMarker.BOLD_UNDERLINE);
        }
        LinkedHashMap<Position, IDPExport.PositionMarker> rhsMarkers = new LinkedHashMap<>();
        rhsMarkers.put(Position.create(this.alpha.rhs, this.alpha.argument), IDPExport.PositionMarker.BOLD_UNDERLINE);
        return this.c.export(eu) + ":" + this.alpha.rule.export(eu, lhsMarkers, rhsMarkers);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * Returns true, if other is a lsb for the same call argument, but with a
     * (non-strict) superset A, and (non-strict) larget local complexity value.
     * @param ilsb
     * @return
     */
    public boolean subsumes(LocalSizeBound other) {
        if (!this.alpha.equals(other.alpha)) {
            return false;
        }
        return other.A.containsAll(this.A) && other.c.compareTo(this.c) <= 0;
    }

    /**
     * Heuristic to compare two {@link LocaleSizeBounds}.
     * @param other
     * @return if {@code this} should be preferred over {@code other}.
     */
    public boolean isBetter(LocalSizeBound other) {
        if (!this.alpha.equals(other.alpha)) {
            throw new RuntimeException("Trying to compare two LocalSizeBounds with different CallArguments.");
        }
        int comp = this.c.compareTo(other.c);
        return comp < 0 || comp == 0 && this.A.size() <= other.A.size();
    }
}
