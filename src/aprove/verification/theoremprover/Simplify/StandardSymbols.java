package aprove.verification.theoremprover.Simplify;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * Standard function symbols and constants for simplify input
 * @author Andreas Kelle-Emden
 */
public class StandardSymbols {
    public static final FunctionSymbol fsEQ;
    public static final FunctionSymbol fsNEQ;
    public static final FunctionSymbol fsGrt;
    public static final FunctionSymbol fsGrtEQ;
    public static final FunctionSymbol fsLess;
    public static final FunctionSymbol fsLessEQ;
    protected static final HashMap<Integer, FunctionSymbol> fsmapDistinct;
    public static final FunctionSymbol fsStore;
    public static final FunctionSymbol fsSelect;
    public static final FunctionSymbol fsPlus;
    public static final FunctionSymbol fsMinus;
    public static final FunctionSymbol fsTimes;

    public static final FunctionSymbol csTrue;
    public static final FunctionSymbol csFalse;
    public static final FunctionSymbol csPropTrue;
    public static final FunctionSymbol csPropFalse;
    protected static final HashMap<BigInteger, FunctionSymbol> fsmapNumber;



    static{
        // Initialize standard functionsymbols and constants
        fsEQ     = FunctionSymbol.create ("EQ",  2);
        fsNEQ    = FunctionSymbol.create ("NEQ", 2);
        fsGrt    = FunctionSymbol.create (">",   2);
        fsGrtEQ  = FunctionSymbol.create (">=",  2);
        fsLess   = FunctionSymbol.create ("<",   2);
        fsLessEQ = FunctionSymbol.create ("<=",  2);
        fsmapDistinct = new HashMap<Integer, FunctionSymbol>();
        fsStore  = FunctionSymbol.create ("store",  3);
        fsSelect = FunctionSymbol.create ("select", 2);
        fsPlus  = FunctionSymbol.create ("+", 2);
        fsMinus = FunctionSymbol.create ("-", 2);
        fsTimes = FunctionSymbol.create ("*", 2);

        csTrue  = FunctionSymbol.create ("TRUE",  0);
        csFalse = FunctionSymbol.create ("FALSE", 0);
        csPropTrue  = FunctionSymbol.create ("@true",  0);
        csPropFalse = FunctionSymbol.create ("@false", 0);
        fsmapNumber = new HashMap<BigInteger, FunctionSymbol>();
    }

    /**
    * getFsNumber returns a function symbol that represents the given integer value.
    * If the number was not seen before it creates a new function symbol.
    * @param num Integer value
    * @return FunctionSymbol which represents the given value
    */
    public static FunctionSymbol getFsNumber (BigInteger num) {
        FunctionSymbol me = StandardSymbols.fsmapNumber.get(num);
        if (me == null) {
            me = FunctionSymbol.create(num.toString(),0);
            StandardSymbols.fsmapNumber.put (num, me);
        }
        return me;
    }

    /**
    * getFsDistinct returns a function symbol that represents a DISTINCT formula with the given number of formulas.
    * If the number was not seen before it creates a new function symbol.
    * @param num Number of formulas
    * @return FunctionSymbol which represents the DISTINCT formula
    */
    public static FunctionSymbol getFsDistinct (Integer num) {
        if (num < 0) {
            return null;
        }
        FunctionSymbol me = StandardSymbols.fsmapDistinct.get(num);
        if (me == null) {
            me = FunctionSymbol.create("DISTINCT", num.intValue());
            StandardSymbols.fsmapDistinct.put (num, me);
        }
        return me;
    }

}
