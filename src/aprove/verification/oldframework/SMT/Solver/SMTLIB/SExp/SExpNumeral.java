package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.math.*;

public class SExpNumeral extends SExpAtom {

    public static final SExpNumeral ONE = new SExpNumeral(BigInteger.ONE);
    public static final SExpNumeral ZERO = new SExpNumeral(BigInteger.ZERO);

    protected final BigInteger i;

    public SExpNumeral(BigInteger i) {
        assert i.compareTo(BigInteger.ZERO) >= 0;
        this.i = i;
    }

    @Override
    public <T> T accept(SExpVisitor<T> visitor) {
        return visitor.visit(this);
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
        SExpNumeral other = (SExpNumeral) obj;
        if (this.i == null) {
            if (other.i != null) {
                return false;
            }
        } else if (!this.i.equals(other.i)) {
            return false;
        }
        return true;
    }

    public BigInteger getBigInteger() {
        return this.i;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (this.i == null ? 0 : this.i.hashCode());
        return result;
    }

    @Override
    public String toString() {
        return this.i.toString();
    }
}
