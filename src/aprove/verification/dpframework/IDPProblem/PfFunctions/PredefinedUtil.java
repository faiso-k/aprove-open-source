package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *
 * @author Martin Pluecker
 */
public class PredefinedUtil {

    public static TRSFunctionApplication createInt(BigInteger value) {
        return TRSTerm.createFunctionApplication(FunctionSymbol.create(value.toString(), 0));
    }

    /**
     * Decides if a term only contains predefined arithmetic function symbols and variables
     */
    public static boolean onlyPredefinedArithmetic(TRSTerm t, IDPPredefinedMap predefinedMap) {
        Set<FunctionSymbol> leftFs = t.getFunctionSymbols();
        for (FunctionSymbol fs : leftFs) {
            PredefinedFunction<? extends Domain> func = predefinedMap.getPredefinedFunction(fs);
            if ((func == null || !func.isArithmetic()) && !predefinedMap.isInt(fs, DomainFactory.INTEGERS)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Decides if a term only contains predefined function symbols and variables
     */
    public static boolean onlyPredefined(TRSTerm t, IDPPredefinedMap predefinedMap) {
        Set<FunctionSymbol> leftFs = t.getFunctionSymbols();
        for (FunctionSymbol fs : leftFs) {
            if (!predefinedMap.isPredefined(fs)) {
                return false;
            }
        }
        return true;
    }

}
