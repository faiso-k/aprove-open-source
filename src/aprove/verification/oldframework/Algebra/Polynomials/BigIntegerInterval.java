package aprove.verification.oldframework.Algebra.Polynomials;

import java.math.*;

import immutables.*;

/**
 * @author Andreas Capellmann
 * @author Carsten Fuhs
 */
public class BigIntegerInterval implements Immutable {

    public final BigInteger max;
    public final BigInteger min;

    public BigIntegerInterval(BigInteger min, BigInteger max) {
        this.min = min;
        this.max = max;
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder("[");
        b.append(this.min);
        b.append(",");
        b.append(this.max);
        b.append("]");

        return b.toString();
    }
}
