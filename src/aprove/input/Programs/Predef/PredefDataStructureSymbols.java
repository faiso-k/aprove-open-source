package aprove.input.Programs.Predef;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** class that should contain all pre-defined symbols
 */
public class PredefDataStructureSymbols {

    private static Set<Symbol> predefs = new HashSet<Symbol>();

    /** removes all pre-defined symbols
     */
    public static void clear() {
        PredefDataStructureSymbols.predefs.clear();
    }

    /** checks wheter a Symbol with that name is a predefined symbol
     * @param name the name of the symbol to check
     * @return true iff a symbol with that name is known to be predefined
     */
    public static boolean isPredefinedSymbol(String name) {
        for(Symbol sym : PredefDataStructureSymbols.predefs) {
            if (sym.getName().equals(name)) {
                return true;
            }
        }
        return false;
    }

    /** checks whether the passed symbol is a predefined symbol
     * @param sym the symbol to check
     * @return true iff this symbol is known to be a predefined symbol
     */
    public static boolean isPredefinedSymbol(Symbol sym) {
        return PredefDataStructureSymbols.predefs.contains(sym);
    }

    /** adds a symbol to the predefined symbols
     * @param sym the symbol to add
     */
    public static void addPredefinedSymbol(Symbol sym) {
        PredefDataStructureSymbols.predefs.add(sym);
    }

    /** adds all of the passed symbols to the predefined symbols
     * @param syms the symbols to add
     */
    public static void addPredefinedSymbols(Collection<? extends Symbol> syms) {
        PredefDataStructureSymbols.predefs.addAll(syms);
    }

    /** adds all symbols of the TypeDefinition to the predefined symbols
     * @param td the TypeDefinition defining the predefined symbols
     */
    public static void addPredefinedSymbols(TypeDefinition td) {
        PredefDataStructureSymbols.addPredefinedSymbols(td.getDeclaredSymbols());
    }


    /** get all predefined symbols
     * @return the set all predefined symbols
     */
    public static Set<Symbol> getPredefinedSymbols() {
        return PredefDataStructureSymbols.predefs;
    }

    public static Set<ConstructorSymbol> getPredefinedConstructorSymbols() {
        Set<ConstructorSymbol> predefConsSyms = new HashSet<ConstructorSymbol>();
        for(Symbol sym : PredefDataStructureSymbols.predefs) {
            if (sym instanceof ConstructorSymbol) {
                predefConsSyms.add((ConstructorSymbol)sym);
            }
        }
        return predefConsSyms;
    }
}
