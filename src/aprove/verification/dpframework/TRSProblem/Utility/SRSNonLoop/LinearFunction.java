package aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop;

import immutables.*;

/**
 * represents a (very) simple LinearFunction a * x + b <br>
 * where a = lin and b = abs
 * @author Tim Enger
 */
public class LinearFunction implements Immutable {

    private final int a;
    private final int b;
    private final int hashCode;

    public LinearFunction(int a, int b) {
        this.a = a;
        this.b = b;
        this.hashCode = this.newHashCode();
    }

    public LinearFunction add(int summand) {
        return new LinearFunction(this.a, this.b + summand);
    }

    public LinearFunction multiply(int factor) {
        int i = this.a * factor;
        int j = this.b * factor;
        return new LinearFunction(i, j);
    }

    public int getAbs() {
        return this.b;
    }

    public int getLin() {
        return this.a;
    }

    public int newHashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + this.a;
        result = prime * result + this.b;
        return result;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(Object obj) {
        if (this.hashCode != obj.hashCode()) {
            return false;
        }

        if (obj instanceof LinearFunction) {
            LinearFunction f = (LinearFunction) obj;
            return this.a == f.getLin() && this.b == f.getAbs();
        }
        return false;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        if (this.a > 0) {
            if (this.a != 1) {
                sb.append(this.a);
            }
            sb.append("k");
        }
        if (this.b > 0) {
            sb.append("+");
            sb.append(this.b);
        }
        return sb.toString();
    }

    public boolean isFitableIn(LinearFunction other) {
        if (this.a == other.a) {
            return this.b <= other.b && (other.b - this.b) % this.a == 0;
        }
        return this.a < other.a && other.a % this.a == 0 && Math.abs(other.b - this.b) % this.a == 0;
    }
}
