package aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp;

import java.math.*;

public class SExpHexadecimal extends SExpNumeral {

    SExpHexadecimal(BigInteger i) {
        super(i);
    }

    @Override
    public String toString() {
        return "#x" + this.i.toString(16);
    }

}
