package aprove.verification.complexity.LowerBounds.BasicStructures;

import aprove.verification.dpframework.BasicStructures.*;

/** Extends the concept of positions from terms to rules. */
public class RulePosition {

    public enum Side {
        LEFT, RIGHT
    }

    public final Side side;
    public final Position pos;

    public RulePosition(Side side, Position pos) {
        this.side = side;
        this.pos = pos;
    }

    @Override
    public String toString() {
        return this.side.toString() + this.pos;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.pos == null) ? 0 : this.pos.hashCode());
        result = prime * result + ((this.side == null) ? 0 : this.side.hashCode());
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
        RulePosition other = (RulePosition) obj;
        if (this.pos == null) {
            if (other.pos != null) {
                return false;
            }
        } else if (!this.pos.equals(other.pos)) {
            return false;
        }
        if (this.side != other.side) {
            return false;
        }
        return true;
    }
}
