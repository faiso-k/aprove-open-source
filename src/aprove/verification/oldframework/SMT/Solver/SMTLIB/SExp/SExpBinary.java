package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.math.*;

public class SExpBinary extends SExpNumeral {

    SExpBinary(BigInteger i) {
        super(i);
    }

    @Override
    public <T> T accept(SExpVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String toString() {
        return "#x" + this.i.toString(2);
    }
}
