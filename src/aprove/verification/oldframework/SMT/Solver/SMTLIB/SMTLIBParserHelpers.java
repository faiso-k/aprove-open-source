package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;

public class SMTLIBParserHelpers {
    public static Sort parseSort(SExp sExp) {
        if (SMTLIBSymbols.Int.equals(sExp)) {
            return SInt.representative;
        }
        if (SMTLIBSymbols.Bool.equals(sExp)) {
            return SBool.representative;
        }
        throw new RuntimeException("could not parse sort: " + sExp);
    }
}
