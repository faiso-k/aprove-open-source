package aprove.verification.diophantine;

import java.math.*;

import aprove.*;
import immutables.*;

/**
 * Numbers from the mathematical integers \cup {-\infty, \infty}
 *
 * @author Carsten Fuhs
 */
public class InfInt implements Immutable, Comparable<InfInt> {

    public enum InfIntType implements Comparable<InfIntType> {
        MINUS_INF, FINITE, PLUS_INF; // the order matters!
    }

    public static final InfInt MINUS_INFINITY =
            new InfInt(InfIntType.MINUS_INF, null);
    public static final InfInt PLUS_INFINITY =
            new InfInt(InfIntType.PLUS_INF, null);

    // invariant: type is FINITE iff number != null
    private final InfIntType type;
    private final BigInteger number;

    private InfInt(InfIntType type, BigInteger number) {
        if (Globals.useAssertions) {
            // type is FINITE iff number != null, expressed via XOR
            assert type == InfIntType.FINITE ^ number == null;
        }
        this.type = type;
        this.number = number;
    }

    /**
     * @param number - non-null
     * @return an InfInt with value <code>number</code>
     */
    public static InfInt create(BigInteger number) {
        assert number != null;
        return new InfInt(InfIntType.FINITE, number);
    }

    @Override
    public int compareTo(InfInt o) {
        if (this.type == InfIntType.FINITE && o.type == InfIntType.FINITE) {
            return this.number.compareTo(o.number);
        } else {
            return this.type.compareTo(o.type);
        }
    }

    public InfInt plus(InfInt o) {
        switch (this.type) {
        case FINITE :
            switch (o.type) {
            case MINUS_INF :
            case PLUS_INF :
                return o;
            case FINITE :
                BigInteger newNumber = this.number.add(o.number);
                return InfInt.create(newNumber);
            }
        case MINUS_INF :
            switch (o.type) {
            case FINITE :
            case MINUS_INF :
                return this;
            case PLUS_INF :
                return null; // different infinities make no sense together
            }
        case PLUS_INF :
            switch (o.type) {
            case FINITE :
            case PLUS_INF :
                return this;
            case MINUS_INF :
                return null; // different infinities make no sense together
            }
        }
        throw new RuntimeException("Unexpected case " + this.type + " + "
                + o.type + '!');
    }

    public InfInt minus(InfInt o) {
        switch (this.type) {
        case FINITE :
            switch (o.type) {
            case FINITE :
                BigInteger newNumber = this.number.subtract(o.number);
                return InfInt.create(newNumber);
            case MINUS_INF :
                return InfInt.PLUS_INFINITY;
            case PLUS_INF :
                return InfInt.MINUS_INFINITY;
            }
        case MINUS_INF :
            switch (o.type) {
            case FINITE :
            case PLUS_INF :
                return this;
            case MINUS_INF :
                return null; // subtracting the same infinities makes no sense
            }
        case PLUS_INF :
            switch (o.type) {
            case FINITE :
            case MINUS_INF :
                return this;
            case PLUS_INF :
                return null; // subtracting the same infinities makes no sense
            }
        }
        throw new RuntimeException("Unexpected case " + this.type + " - "
                + o.type + '!');
    }

    public InfInt times(InfInt o) {
        switch (this.type) {
        case FINITE : {
            int thisSignum = this.number.signum();
            switch (o.type) {
            case PLUS_INF :
                 if (thisSignum > 0) {
                     return InfInt.PLUS_INFINITY;
                 } else if (thisSignum < 0) {
                     return InfInt.MINUS_INFINITY;
                 } else {
                     return null; // 0 * \infty makes no sense
                 }
            case MINUS_INF :
                if (thisSignum > 0) {
                    return InfInt.MINUS_INFINITY;
                } else if (thisSignum < 0) {
                    return InfInt.PLUS_INFINITY;
                } else {
                    return null; // 0 * -\infty makes no sense
                }
            case FINITE :
                BigInteger newNumber = this.number.multiply(o.number);
                return InfInt.create(newNumber);
            }
        }
        case MINUS_INF : {
            switch (o.type) {
            case FINITE :
                final int oSignum = o.number.signum();
                if (oSignum > 0) {
                    return InfInt.MINUS_INFINITY;
                } else if (oSignum < 0) {
                    return InfInt.PLUS_INFINITY;
                } else {
                    return null; // 0 * -\infty makes no sense
                }
            case MINUS_INF :
                return InfInt.PLUS_INFINITY;
            case PLUS_INF :
                return InfInt.MINUS_INFINITY;
            }
        }
        case PLUS_INF : {
            switch (o.type) {
            case FINITE :
                final int oSignum = o.number.signum();
                if (oSignum > 0) {
                    return InfInt.PLUS_INFINITY;
                } else if (oSignum < 0) {
                    return InfInt.MINUS_INFINITY;
                } else {
                    return null; // 0 * \infty makes no sense
                }
            case PLUS_INF :
                return InfInt.PLUS_INFINITY;
            case MINUS_INF :
                return InfInt.MINUS_INFINITY;
            }
        }
        }
        throw new RuntimeException("Unexpected case " + this.type + " * "
                + o.type + '!');
    }

    public InfInt negate() {
        switch (this.type) {
        case FINITE :
            BigInteger newNumber = this.number.negate();
            return InfInt.create(newNumber);
        case MINUS_INF :
            return InfInt.PLUS_INFINITY;
        case PLUS_INF :
            return InfInt.MINUS_INFINITY;
        }
        throw new RuntimeException("Unexpected case " + this.type + '!');
    }

    public InfInt max(InfInt other) {
        return this.compareTo(other) > 0 ? this : other;
    }

    public InfInt min(InfInt other) {
        return this.compareTo(other) < 0 ? this : other;
    }

    /**
     * @return the type
     */
    public InfIntType getType() {
        return this.type;
    }

    /**
     * @return the number (null if getType() != InfIntType.FINITE)
     */
    public BigInteger getNumber() {
        return this.number;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((this.number == null) ? 0 : this.number.hashCode());
        result = prime * result
                + ((this.type == null) ? 0 : this.type.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
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
        InfInt other = (InfInt) obj;
        if (this.number == null) {
            if (other.number != null) {
                return false;
            }
        }
        else if (!this.number.equals(other.number)) {
            return false;
        }
        if (this.type != other.type) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        switch (this.type) {
        case FINITE :
            return this.number.toString();
        case MINUS_INF :
            return "-oo";
        case PLUS_INF :
            return "+oo";
        }
        throw new RuntimeException("Unexpected case " + this.type + '!');
    }
}
