package aprove.verification.idpframework.Polynomials;

import java.util.*;

import aprove.verification.idpframework.Core.SemiRings.*;


/**
 *
 * @author MP
 */
public enum Signum {
    Pos(1, "Pos"), StrictPos(2, "StrictPos"), Neg(-1, "Neg"), StrictNeg(-2, "StrictNeg"), Zero(0, "Zero"), Unknown(null, "Unknown"), Wild(null, "Wild"), Contradiction(null, "Contradiction");

    public static <V extends HasSignum> Signum getSignum(final Map<V, Signum> varSignums, final Map<? extends V, BigInt> varExponents) {
        Signum result = Signum.StrictPos;

        for (final Map.Entry<? extends V, BigInt> varExponent : varExponents.entrySet()) {
            Signum varSignum = varSignums.get(varExponent.getKey());
            if (varSignum == null) {
                varSignum = varExponent.getKey().getSignum();
            }

            if (varExponent.getValue().isEven()) {
                result = result.multEvenExponent(varSignum);
            } else {
                result = result.mult(varSignum);
            }
        }

        return result;
    }

    public static <V extends HasSignum> Signum getSignum(final Map<V, Signum> varSignums, final V var) {
        Signum varSignum = varSignums.get(var);
        if (varSignum == null) {
            varSignum = var.getSignum();
        }

        return varSignum;
    }

    public static Signum getSignum(final int signum) {
        if (signum > 0) {
            return StrictPos;
        } else if (signum < 0) {
            return StrictNeg;
        } else {
            return Zero;
        }
    }

    public static <R extends SemiRing<R>> Signum getSignum(final R ringElement) {
        final Integer signum = ringElement.semiCompareTo(ringElement.zero());
        if (signum == null) {
            return null;
        } else if (signum > 0) {
            return StrictPos;
        } else if (signum < 0) {
            return StrictNeg;
        } else {
            return Zero;
        }
    }

    private final Integer id;
    private final String name;

    Signum (final Integer id, final String name) {
        this.id = id;
        this.name = name;
    }

    public Integer getId() {
        return this.id;
    }

    public boolean isStrict () {
        return this == StrictPos || this == StrictNeg;
    }

    public boolean isPos() {
        return this == Zero || this == Pos | this == StrictPos;
    }

    public boolean isNeg() {
        return this == Zero || this == Neg | this == StrictNeg;
    }

    public boolean isDetermined() {
        return this.id != null;
    }

    /**
     * @param other other signum
     * @return true iff the two signums are compatible
     */
    public boolean isCompatible(final Signum other) {
        if (this == Contradiction || other == Contradiction) {
            return false;
        } else if (this == Unknown || other == Unknown) {
            return true;
        } else if (this == Wild || other == Wild) {
            return this == other;
        } else if (this == Pos) {
            return other.id >= -1;
        } else if (this == StrictPos) {
            return other.id > 0;
        } else if (this == Neg) {
            return other.id <= 1;
        } else if (this == StrictNeg) {
            return other.id < 0;
        } else if (this == Zero) {
            return other.id <= 1 && other.id >= -1;
        }
        throw new UnsupportedOperationException("unhandled combination");
    }

    /**
     * Use this method to determine the more specific signum from two neg or two pos signums,
     * e.g. for Pos and StrictPos
     * @return
     * @param other the other Signum
     */
    public Signum moreSpecific(final Signum other) {
        if (this == Contradiction || other == Contradiction) {
            return Contradiction;
        };
        if (this == Unknown) {
            return other;
        } else if (other == Unknown) {
            return this;
        } else if (this == Wild || other == Wild) {
            return Wild;
        }
        if ((this.id < 1 && other.id > 1) || (this.id > 1 && other.id < 1)) {
            throw new IllegalArgumentException("operation not allowed pos and neg");
        }

        if (this == Zero || other == Zero) {
            return Zero;
        }

        if ((this.id > 0 && other.id < 0) || (this.id < 0 && other.id > 0)) {
            return Zero;
        }
        if (this.id > 0) {
            if (other.id > this.id) {
                return other;
            } else {
                return this;
            }
        } else {
            if (other.id < this.id) {
                return other;
            } else {
                return this;
            }
        }
    }

    /**
     * Use this method to determine the more specific signum from two neg or two pos signums,
     * e.g. for Pos and StrictPos
     * @param other the other Signum
     * @return
     */
    public Signum lessSpecific(final Signum other) {
        if (this == Contradiction || other == Contradiction) {
            return Contradiction;
        };
        if (this == Unknown || other == Zero) {
            return this;
        } else if (other == Unknown || this == Zero) {
            return other;
        } else if (this == Wild || other == Wild) {
            return Wild;
        }

        if ((this.id > 0 && other.id < 0) || (this.id < 0 && other.id > 0)) {
            throw new IllegalArgumentException("operation not allowed pos and neg");
        }

        if (this.id > 0) {
            if (other.id.equals(this.id)) {
                return other;
            } else {
                return Pos;
            }
        } else {
            if (other.id.equals(this.id)) {
                return other;
            } else {
                return Neg;
            }
        }
    }

    public Signum mult(final Signum other) {
        if (this == Contradiction || other == Contradiction) {
            return Contradiction;
        } else if (this == Zero || other == Zero) {
            return Zero;
        } else if (this == Unknown || other == Unknown) {
            return Unknown;
        } else if (this == Wild || other == Wild) {
            return Wild;
        } else {
            switch (this.id.intValue() * other.id.intValue()) {
            case 1 : return Pos;
            case 2 : return Pos;
            case 4 : return StrictPos;
            case -1 : return Neg;
            case -2 : return Neg;
            case -4 : return StrictNeg;
            }
        }
        throw new UnsupportedOperationException("check mult procedure");
    }

    public Signum multEvenExponent(final Signum other) {
        if (this == Contradiction || other == Contradiction) {
            return Contradiction;
        } else if (this == Zero || other == Zero) {
            return Zero;
        } else if (this == Unknown) {
            return Unknown;
        } else if (other == Unknown) {
            return this.makeNonStrict();
        } else if (other == Wild) {
            return this.makeNonStrict();
        } else {
            return this;
        }
    }

    public Signum intersect(final Signum other) {
        if (this == Contradiction || other == Contradiction) {
            return Contradiction;
        } else if (this == Zero || other == Zero) {
            return Zero;
        } else if (this == Unknown || this == Wild) {
            return other;
        } else if (other == Unknown || other == Wild) {
            return this;
        } else {
            if (this.isPos() != other.isPos() || this.isNeg() != other.isNeg()) {
                if (this.isStrict() || other.isStrict()) {
                    return Contradiction;
                } else {
                    return Zero;
                }
            } else {
                if (this.isStrict()) {
                    return this;
                } else {
                    return other;
                }
            }
        }
    }

    public Signum union(final Signum other) {
        if (this == Contradiction || other == Contradiction) {
            return Contradiction;
        } else if (this == Wild || other == Wild) {
            return Wild;
        } else if (this == Unknown || other == Unknown) {
            return Unknown;
        } else if (this == Zero) {
            return other.makeNonStrict();
        } else if (other == Zero) {
            return this.makeNonStrict();
        } else {
            if (this.isPos() != other.isPos() || this.isNeg() != other.isNeg()) {
                return Wild;
            } else {
                if (this.isStrict() && other.isStrict()) {
                    return this;
                } else {
                    return this.makeNonStrict();
                }
            }
        }
    }

    public Signum negate() {
        switch (this) {
        case Contradiction : return Contradiction;
        case Neg : return Pos;
        case Pos : return Neg;
        case StrictNeg : return StrictPos;
        case StrictPos : return StrictNeg;
        case Unknown : return Unknown;
        case Wild : return Wild;
        case Zero : return Zero;
        }
        throw new UnsupportedOperationException("negation case not known");
    }

    public Signum makeStrict() {
        switch (this) {
        case Pos : return StrictPos;
        case StrictPos : return StrictPos;
        case Neg : return StrictNeg;
        case StrictNeg : return StrictNeg;
        default:
            throw new UnsupportedOperationException("strict not allowed here: " + this.toString());
        }
    }

    public Signum makeNonStrict() {
        switch (this) {
        case Pos : return Pos;
        case StrictPos : return Pos;
        case Neg : return Neg;
        case StrictNeg : return Neg;
        default:
            throw new UnsupportedOperationException("strict not allowed here: " + this.toString());
        }
    }

    @Override
    public String toString() {
        return this.name;
    }
}
