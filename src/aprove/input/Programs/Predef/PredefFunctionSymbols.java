package aprove.input.Programs.Predef;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** class that should contain all names of pre-defined function symbols
 */
public class PredefFunctionSymbols {

    // stores function name -> argument sorts and return sort
    private static Map<String, Pair<List<String>, String>> predefSig =
        new HashMap<String, Pair<List<String>, String>>();

    // stores fixity and precedence for functions
    private static Map<String, Pair<Integer, Integer>> predefPrecedence = new HashMap<String, Pair<Integer, Integer>>();

    private static int minPrecedence = -1;

    /** removes all predefined function names and all precedences
     */
    public static void clear() {
        PredefFunctionSymbols.predefSig.clear();
        PredefFunctionSymbols.predefPrecedence.clear();
        PredefFunctionSymbols.minPrecedence = -1;
    }

    /** gives access to the map that stores the names of argument sort
     * and the name of the return sort for a predefined function
     * @return the map used to store the argument names for a predefined function
     */
    public static Map<String, Pair<List<String>, String>> getPredefinedFunctionsSorts() {
        return PredefFunctionSymbols.predefSig;
    }

    /** checks whether a function with that name is predefined
     * @param funcName the name of the symbol to check
     * @return true iff a symbol with that name is known to be predefined
     */
    public static boolean isPredefinedFunction(final String funcName) {
        return PredefFunctionSymbols.predefSig.keySet().contains(funcName);
    }

    /** checks whether the passed symbol has the name of a predefined function symbol
     * @param sym the symbol to check
     * @return true iff this symbol is known to be a predefined symbol
     */
    public static boolean isPredefinedSymbol(final Symbol sym) {
        return PredefFunctionSymbols.predefSig.keySet().contains(sym.getName());
    }

    /** adds all the passed predefined functions, their argument types names, their return type name, and their precedence
     * @param funcNames the names, argument types names, return type name, and the pair (fixity,precedence) of predefined functions to add (any previous entries will be overwritten)
     */
    public static void addPredefinedFunctions(final Map<? extends String, ? extends Triple<List<String>, String, Pair<Integer, Integer>>> funcNamesAndArgs) {
        for (final Map.Entry<? extends String, ? extends Triple<List<String>, String, Pair<Integer, Integer>>> e : funcNamesAndArgs.entrySet()) {
            final String funcName = e.getKey();
            final Triple<List<String>, String, Pair<Integer, Integer>> argNamesAndPrecedence = e.getValue();
            PredefFunctionSymbols.predefSig.put(funcName, new Pair<List<String>, String>(argNamesAndPrecedence.x, argNamesAndPrecedence.y));
            PredefFunctionSymbols.predefPrecedence.put(funcName, argNamesAndPrecedence.z);
            if (argNamesAndPrecedence.z != null) {
                PredefFunctionSymbols.minPrecedence = Math.min(PredefFunctionSymbols.minPrecedence, argNamesAndPrecedence.z.y);
            }
        }
    }

    /** gets the fixity of a predefined function, should be set for infix operators previously
     * @param funcName name of a predefined function
     * @return the fixity of the specified predefined function, or FunctionSymbol.NOTINFIX if it was not set
     */
    public static Integer getFixity(final String funcName) {
        final Pair<Integer, Integer> fixityAndPrecedence = PredefFunctionSymbols.predefPrecedence.get(funcName);
        if (fixityAndPrecedence != null) {
            return fixityAndPrecedence.x;
        } else {
            return SyntacticFunctionSymbol.NOTINFIX;
        }
    }

    /** gets the precedence of a predefined function, should be set for infix operators previously
     * @param funcName name of a predefined function
     * @return the precedence of the specified predefined function, or null if the level was not set
     */
    public static Integer getPrecedence(final String funcName) {
        final Pair<Integer, Integer> fixityAndPrecedence = PredefFunctionSymbols.predefPrecedence.get(funcName);
        if (fixityAndPrecedence != null) {
            return fixityAndPrecedence.y;
        } else {
            return null;
        }
    }

    /** gets the pair of fixity and precedence for a function
     * @param funcName name of a predefined function
     * @return the pair (fixity,precedence) of the specified predefined function, or null if not set
     */
    public static Pair<Integer, Integer> getFixityAndPrecedence(final String funcName) {
        return PredefFunctionSymbols.predefPrecedence.get(funcName);
    }

    /** gets the minimum precedence over all stored function symbols
     * @return minimum precedence that a function stored in here has
     */
    public static Integer getMinPrecedence() {
        return PredefFunctionSymbols.minPrecedence;
    }
}
