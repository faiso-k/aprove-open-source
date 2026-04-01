package aprove.verification.oldframework.WeightedIntTrs;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

public class Util {

    public static MinMaxExpr renameVariablesAccordingToStartTerm(TRSFunctionApplication startTerm, MinMaxExpr poly, List<String> args) {
        Map<String, MinMaxExpr> sigma = new LinkedHashMap<>();
        Iterator<String> it = args.iterator();
        for (TRSTerm t: startTerm.getArguments()) {
            String varName = it.next();
            if (t.isVariable()) {
                sigma.put(varName, MinMaxExpr.createVar(t.getName()));
            } else if (t.isConstant()) {
                sigma.put(varName, MinMaxExpr.createInt(new BigInteger(t.getName())));
            } else {
                throw new RuntimeException();
            }
        }
        return poly.substitute(sigma);
    }

}
