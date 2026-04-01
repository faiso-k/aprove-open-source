/**
 *
 */
package aprove.verification.complexity.AcdtProblem.Utils;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public class DefinedPositionsTree implements Immutable {
    public final Position p;
    public final TRSFunctionApplication t;
    public final ImmutableArrayList<DefinedPositionsTree> sub;
    public final int hashCode;

    private DefinedPositionsTree(Position p, TRSFunctionApplication t,
            ImmutableArrayList<DefinedPositionsTree> sub) {
        this.p = p;
        this.t = t;
        this.sub = sub;
        this.hashCode = this.computeHashCode();
    }

    public static DefinedPositionsTree create(Position p, TRSFunctionApplication t,
            ImmutableArrayList<DefinedPositionsTree> sub) {
        return new DefinedPositionsTree(p, t, sub);
    }

    public int computeHashCode() {
        final int prime = 719;
        int result = 1;
        result = prime * result + ((this.p == null) ? 0 : this.p.hashCode());
        result = prime * result + ((this.sub == null) ? 0 : this.sub.hashCode());
        result = prime * result + ((this.t == null) ? 0 : this.t.hashCode());
        return result;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
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
        DefinedPositionsTree other = (DefinedPositionsTree) obj;
        if (this.p == null) {
            if (other.p != null) {
                return false;
            }
        } else if (!this.p.equals(other.p)) {
            return false;
        }
        if (this.sub == null) {
            if (other.sub != null) {
                return false;
            }
        } else if (!this.sub.equals(other.sub)) {
            return false;
        }
        if (this.t == null) {
            if (other.t != null) {
                return false;
            }
        } else if (!this.t.equals(other.t)) {
            return false;
        }
        return true;
    }

}