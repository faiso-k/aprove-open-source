/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.utility;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;


public class Utils {

    public static boolean isInteger(String value) {
        char [] chars = new char[value.length()];
        if (chars.length == 0) {
            return false;
        }
        value.getChars(0, chars.length, chars, 0);
        if (!Character.isDigit(chars[0]) && !Character.isLetter('-')) {
            return false;
        }
        for (int i = chars.length-1; i >= 0; i--) {
            if (!Character.isDigit(chars[i])) {
                return false;
            }
        }
        return true;
    }


    public static boolean isCondRule(GeneralizedRule rule, IDPPredefinedMap predefinedMap) {
        if (!rule.getRight().isVariable()) {
            TRSFunctionApplication faR = (TRSFunctionApplication) rule.getRight();
            TRSFunctionApplication faL = rule.getLeft();
            for (TRSTerm arg : faR.getArguments()) {
                if (!faL.getArguments().contains(arg)) {
                    if (arg.isVariable()) {
                        return false;
                    } else {
                        TRSFunctionApplication faArg = (TRSFunctionApplication) arg;
                        PredefinedFunction<? extends Domain> func = predefinedMap.getPredefinedFunction(faArg.getRootSymbol());
                        if (func == null || (!func.isBoolean() && !func.isRelation())) {
                            return false;
                        }
                    }
                }
            }
            return true;
        } else {
            return false;
        }
    }

}
