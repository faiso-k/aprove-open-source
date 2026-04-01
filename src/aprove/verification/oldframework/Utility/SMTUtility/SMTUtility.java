package aprove.verification.oldframework.Utility.SMTUtility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Some helper functions for SMT encoding
 *
 * @author Andreas Kelle-Emden
 */
public class SMTUtility {

    /**
     * Calculate mappings from SMTLIBVariables to names that are compatible with
     * the YICES input format and backwards.
     *
     * @param varSet set of SMTLIBVariables
     * @return pair of the two mappings
     */
    public static Pair<Map<SMTLIBVariable, String>, Map<String, SMTLIBVariable>> getYICESSMTNameMap(final Set<SMTLIBVariable> varSet) {
        final Map<SMTLIBVariable, String> varNameMap = new LinkedHashMap<SMTLIBVariable, String>();
        final Map<String, SMTLIBVariable> retrMap = new LinkedHashMap<String, SMTLIBVariable>();
        final Set<String> stringSet = new LinkedHashSet<String>();
        for (final SMTLIBVariable var : varSet) {
            boolean createNew = false;
            String varName = var.getName();
            if (varName.contains(":")) {
                varName = varName.replace(":", "colon");
                createNew = true;
            }
            if (stringSet.contains(varName)) {
                createNew = true;
            } else {
                stringSet.add(varName);
            }

            if (createNew) {
                boolean ok = false;
                while (!ok) {
                    if (!stringSet.contains(varName)) {
                        ok = true;
                    } else {
                        varName += "_";
                    }
                }
            }
            varNameMap.put(var, varName);
            retrMap.put(varName, var);
        }
        return new Pair<Map<SMTLIBVariable, String>, Map<String, SMTLIBVariable>>(varNameMap, retrMap);
    }

    /**
     * Calculate mappings from function symbols to names that are compatible with
     * the YICES input format and backwards.
     *
     * @param symSet set of function symbols
     * @return pair of the two mappings
     */
    public static Pair<Map<FunctionSymbol, String>, Map<String, FunctionSymbol>> getYICESSymNameMap(final Set<FunctionSymbol> symSet) {
        final Map<FunctionSymbol, String> symNameMap = new LinkedHashMap<>();
        final Map<String, FunctionSymbol> retrMap = new LinkedHashMap<>();
        for (final FunctionSymbol sym : symSet) {
            String symName = sym.getArity() + "_" + sym.getName();
            if (symName.contains(":")) {
                symName = symName.replace(":", "colon");

                FunctionSymbol newSym = FunctionSymbol.create(symName, sym.getArity());
                boolean ok = !symSet.contains(newSym);
                while (!ok) {
                    symName += "_";
                    newSym = FunctionSymbol.create(symName, sym.getArity());
                    ok = !symSet.contains(newSym);
                }
            }
            // yices does not like function names starting with numbers, so just prepend "_"
            symName = "_" + symName;
            symNameMap.put(sym, symName);
            retrMap.put(symName, sym);
        }
        return new Pair<>(symNameMap, retrMap);
    }

    /**
     * Calculate mappings from variables to names that are compatible with
     * the YICES input format and backwards.
     *
     * @param symSet set of variables
     * @return pair of the two mappings
     */
    public static Pair<Map<TRSVariable, String>, Map<String, TRSVariable>> getYICESVarNameMap(final Set<TRSVariable> varSet) {
        final Map<TRSVariable, String> varNameMap = new LinkedHashMap<TRSVariable, String>();
        final Map<String, TRSVariable> varRetrMap = new LinkedHashMap<String, TRSVariable>();
        for (final TRSVariable var : varSet) {
            boolean createNew = false;
            String varName = var.getName();
            if (varName.contains(":")) {
                varName = varName.replace(":", "colon");
                createNew = true;
            }

            if (createNew) {
                boolean ok = false;
                while (!ok) {
                    final TRSVariable newVar = TRSTerm.createVariable(varName);
                    if (!varSet.contains(newVar)) {
                        ok = true;
                    } else {
                        varName += "_";
                    }
                }
            }
            varName = "_" + varName;
            varNameMap.put(var, varName);
            varRetrMap.put(varName, var);
        }
        return new Pair<Map<TRSVariable, String>, Map<String, TRSVariable>>(varNameMap, varRetrMap);
    }

}
