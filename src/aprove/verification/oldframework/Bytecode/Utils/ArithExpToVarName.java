package aprove.verification.oldframework.Bytecode.Utils;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
/**
 * Converts an arithmetic expression to a potential variable name that reflects its semantics. E.g., x + y is transformed to sum~x~y.
 */
public class ArithExpToVarName {

    private static Map<String, String> stringRepresentations = new LinkedHashMap<>();
    static {
        stringRepresentations.put("+_2", "sum");
        stringRepresentations.put("*_2", "times");
        stringRepresentations.put("-_1", "minus");
        stringRepresentations.put("-_2", "minus");
        stringRepresentations.put("/_2", "div");
        stringRepresentations.put("%_2", "mod");
    }

    public static String getVarName(ITerm<?> arg) {
        if (arg instanceof IVariable<?>) {
            return ((IVariable<?>) arg).getName();
        }
        IFunctionApplication<?> fa = ((IFunctionApplication<?>) arg);
        IFunctionSymbol<?> f = fa.getRootSymbol();
        if (stringRepresentations.containsKey(f.toString())) {
            String res = stringRepresentations.get(f.toString());
            if (!fa.isConstant()) {
                res += "~";
                for (int i = 0; i < f.getArity() - 1; i++) {
                    res += getVarName(fa.getArgument(i)) + "~";
                }
                res += getVarName(fa.getArgument(f.getArity() - 1));
            }
            return res;
        } else {
            try {
                Integer.parseInt(arg.toString());
                return "cons_" + arg.toString();
            } catch (NumberFormatException e) {
                return "x";
            }
        }
    }

    public static String getVarName(TRSTerm arg) {
        if (arg instanceof TRSVariable) {
            return ((TRSVariable) arg).getName();
        }
        TRSFunctionApplication fa = ((TRSFunctionApplication) arg);
        FunctionSymbol f = fa.getRootSymbol();
        if (stringRepresentations.containsKey(f.toString())) {
            String res = stringRepresentations.get(f.toString());
            if (!fa.isConstant()) {
                res += "~";
                for (int i = 0; i < f.getArity() - 1; i++) {
                    res += getVarName(fa.getArgument(i)) + "~";
                }
                res += getVarName(fa.getArgument(f.getArity() - 1));
            }
            return res;
        } else {
            try {
                Integer.parseInt(arg.toString());
                return "cons_" + arg.toString();
            } catch (NumberFormatException e) {
                return "x";
            }
        }
    }

}
