package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/** Helpers for Integers
 */
public class IntegerTools {


    private static final String IntegerPredefFunctionsPropertiesFile = "IntegerPredefFunctions.properties";


    private static final String intTypeName = AbstractIntegerPredefItem.getIntTypeName();
    private static final String zeroName = AbstractIntegerPredefItem.getZeroName();
    private static final String succName = AbstractIntegerPredefItem.getSuccName();
    private static final String predName = AbstractIntegerPredefItem.getPredName();


    /** shortcut */
    private static class TZeroSuccPred extends Triple<ConstructorSymbol,ConstructorSymbol,ConstructorSymbol> {
        TZeroSuccPred(ConstructorSymbol x, ConstructorSymbol y, ConstructorSymbol z) {
            super(x,y,z);
        }
    }


    // used for caching
    private static TypeContext lastTypeContext = null;
    private static TZeroSuccPred lastZeroSuccPred = null;



    /** returns the ConstructorSymbols for zero, succ, and pred
     *
     * @param typeContext the TypeContext the Integers are defined in
     * @return the triple (zero,succ,pred)
     */
    private static TZeroSuccPred getIntegerSymbols(TypeContext typeContext) {

        // cache => here it is assumed that once the integer symbols are created they are not changed
        if (IntegerTools.lastTypeContext == typeContext) {
            return IntegerTools.lastZeroSuccPred;
        }



        TypeDefinition intTypeDef = typeContext.getTypeDef(IntegerTools.intTypeName);

        // the Integer TypeDef does not exist yet => ERROR
        if(intTypeDef == null) {
            throw new RuntimeException("Error: The Integer Type Definition was not found.");
        }


        ConstructorSymbol zero=null,succ=null,pred=null;

        // read the Integer Symbols
        for(Symbol sym : intTypeDef.getDeclaredSymbols()) {
            if (sym.getName().equals(IntegerTools.zeroName)) {
                zero = (ConstructorSymbol)sym;
            } else if (sym.getName().equals(IntegerTools.succName)) {
                succ = (ConstructorSymbol)sym;
            } else if (sym.getName().equals(IntegerTools.predName)) {
                pred = (ConstructorSymbol)sym;
            } else {
                throw new RuntimeException("Error: Symbol ''"+sym.getName()+"'' in Integer type definition is unknown.");
            }
        }

        if ( (zero == null) || (succ == null) || (pred == null) ) {
            if ( (zero == null) && (succ == null) && (pred == null) ) {
                throw new RuntimeException("Error: Integer data structure symbols do not exist!");
            }
            else {
                throw new RuntimeException("Error: Some Integer data structure symbols exist, while others do not.");
            }
        }

        // filling cache
        IntegerTools.lastZeroSuccPred = new TZeroSuccPred(zero,succ,pred);
        IntegerTools.lastTypeContext = typeContext;

        return IntegerTools.lastZeroSuccPred;
    }




    /** returns the Integer Type from the typeContext
     * @param typeContext the Type Context to look for Integers in
     * @return the Integer DefTerm
     */
    public static AlgebraTerm getIntType(TypeContext typeContext) {
        return typeContext.getTypeDef(IntegerTools.intTypeName).getDefTerm();
    }

    /** returns the Integer sort from the program
     * @param program Program to look for integer sort in
     * @return the sort of integers
     */
    @Deprecated
    public static Sort getIntSort(Program program) {
        return program.getSort(IntegerTools.intTypeName);
    }


    /** checks whether a Term t is built only from symbols of the Integer Data Structure
     * and does not contain succ and pred inside one another
     * @param t Term to check
     * @param typeContext TypeContext the Integers are defined in
     * @return true iff t is built only from zero, succ, or pred
     */
    public static boolean isIntegerTerm(AlgebraTerm t, TypeContext typeContext) {
        TZeroSuccPred zeroSuccPred = IntegerTools.getIntegerSymbols(typeContext);
        Set<Symbol> disallowedSymbols = new HashSet<Symbol>();
        if (IntegerTools.isIntSymbol(t.getSymbol(), zeroSuccPred)) {
            disallowedSymbols = IntegerTools.getDisallowedSymbols(t.getSymbol(), zeroSuccPred);
        }

        return IntegerTools.isIntegerTerm(t,disallowedSymbols,zeroSuccPred,typeContext);
    }

    // recursive Helper for isIntegerTerm(Term)
    private static boolean isIntegerTerm(AlgebraTerm t, Set<Symbol> disallowedSymbols, TZeroSuccPred zeroSuccPred, TypeContext typeContext) {
        ConstructorSymbol zero = zeroSuccPred.x;
        ConstructorSymbol succ = zeroSuccPred.y;
        ConstructorSymbol pred = zeroSuccPred.z;

        if (t.getSymbol().equals(zero) || t.getSymbol().equals(succ) || t.getSymbol().equals(pred)) {
            for(AlgebraTerm arg : t.getArguments()) {
                if (disallowedSymbols.contains(arg.getSymbol()))
                 {
                    return false; // subterm starts with a non-allowed symbol
                }

                if(!IntegerTools.isIntegerTerm(arg,disallowedSymbols,zeroSuccPred,typeContext))
                 {
                    return false;  // subterm is not an Integer-term
                }
            }
            return true;  // all subterms are Integer-terms and root-symbol is zero, succ, or pred
        }
        return false; // current root-symbol is neither zero, succ, nor pred
    }




    /** checks whether a term contains only valid Integer terms,
     * e.g. would return false, if a pred occurs inside a succ
     * @param t Term to check
     * @param typeContext TypeContext the Integers are defined in and that defines the type of the root symbol of t
     * @return true iff all Integer Terms are well formed
     */
    public static boolean containsOnlyValidIntegerTerms(AlgebraTerm t, TypeContext typeContext) {
        return IntegerTools.containsOnlyValidIntegerTerms(t, new HashSet<Symbol>(), IntegerTools.getIntegerSymbols(typeContext));
    }

    // private helper for containsOnlyValidIntegerTerms
    private static boolean containsOnlyValidIntegerTerms(AlgebraTerm t, Set<Symbol> disallowedSymbols, TZeroSuccPred zeroSuccPred) {
        if (t.isVariable())
         {
            return true; // Variables do not need to be considered any further
        }

        if(IntegerTools.isIntSymbol(t.getSymbol(),zeroSuccPred)) {
            disallowedSymbols = IntegerTools.getDisallowedSymbols(t.getSymbol(),zeroSuccPred);
        }

        for(AlgebraTerm arg : t.getArguments()) {
            if(disallowedSymbols.contains(arg.getSymbol()))
             {
                return false; // subterm starts with a non-allowed symbol
            }

            if(!IntegerTools.containsOnlyValidIntegerTerms(arg,disallowedSymbols,zeroSuccPred))
             {
                return false; // subterm contains non-well formed Integer terms
            }
        }

        return true;
    }



    /** returns whether the symbol sym is an Integer Symbol
     * @param sym symbol to test
     * @param typeContext TypeContext to look for Integers in
     * @return true iff sym is an Integer symbol
     */
    public static boolean isIntSymbol(Symbol sym, TypeContext typeContext) {
        TZeroSuccPred zeroSuccPred = IntegerTools.getIntegerSymbols(typeContext);
        return IntegerTools.isIntSymbol(sym, zeroSuccPred);
    }


    /** returns whether the symbol sym is an Integer Symbol using the passed constructors
     * @param sym symbol to test
     * @param zeroSuccPred the result of a call to getIntegerSymbols(TypeContext)
     * @return true iff sym is an Integer symbol
     */
    private static boolean isIntSymbol(Symbol sym, TZeroSuccPred zeroSuccPred) {
        Set<Symbol> intSyms = new HashSet<Symbol>(Arrays.asList(zeroSuccPred.x, zeroSuccPred.y, zeroSuccPred.z));
        return intSyms.contains(sym);
    }


    /** gets the symbols that a Term inside an argument of sym must not consist of
     *  e.g. for succ the set consists of pred
     * @param cons the symbol for which argument restrictions are to be generated
     * @param typeContext the TypeContext that defines the Integers
     * @return a set of symbols not allowed inside arugments of sym
     */
    public static Set<Symbol> getDisallowedSymbols(Symbol cons, TypeContext typeContext) {
        return IntegerTools.getDisallowedSymbols(cons, IntegerTools.getIntegerSymbols(typeContext));
    }

    /** gets the symbols that a Term inside an argument of sym must not consist of
     *  e.g. for succ the set consists of pred
     * @param cons the symbol for which argument restrictions are to be generated
     * @param zeroSuccPred the result of a call to getIntegerSymbols(TypeContext)
     * @return a set of symbols not allowed inside arugments of sym
     */
    private static Set<Symbol> getDisallowedSymbols(Symbol cons, TZeroSuccPred zeroSuccPred) {
        Symbol zero = zeroSuccPred.x;
        Symbol succ = zeroSuccPred.y;
        Symbol pred = zeroSuccPred.z;

        Set<Symbol> disallowedSyms = new HashSet<Symbol>();

        if(cons.equals(zero)) {
            // does not have arguments
        }
        else if(cons.equals(succ)) {
            disallowedSyms.add(pred);
        }
        else if(cons.equals(pred)) {
            disallowedSyms.add(succ);
        }
        else {
            throw new RuntimeException("Error: unknown integer symbol: "+cons);
        }

        return disallowedSyms;
    }




    /** returns the names the integer data structure tokens are assumed to have
     * these tokens are the constructors zero, succ, and pred and the selectors for succ and pred
     * @return the set of names of integer data structure tokens
     */
    public static Set<String> getIntegerDataStructureTokens() {
        Set<String> names = new HashSet<String>();

        names.add(AbstractIntegerPredefItem.getZeroName());
        names.add(AbstractIntegerPredefItem.getSuccName());
        names.add(AbstractIntegerPredefItem.getPredName());
        names.add(AbstractIntegerPredefItem.getSuccSelectorName());
        names.add(AbstractIntegerPredefItem.getPredSelectorName());

        return names;
    }


    /** retrieves the names of predefined Integer functions and the names of their argument types
     * this is done by reading the file whose name is defined in IntegerPredefFunctionsPropertiesFile
     * and adding both sides of the equations (when editing this file, be careful to escape all equality symbols)
     * @return the names of predefined Integer functions mapped to their argument types names, their return sort, and, if these two exists, their fixity and precedence
     */
    public static Map<String, Triple<List<String>,String,Pair<Integer,Integer>>> getIntegerPredefFunctions() {
        Map<String, Triple<List<String>,String,Pair<Integer,Integer>>> predefFuncsArgs = new HashMap<String, Triple<List<String>,String,Pair<Integer,Integer>>>();

        Properties intPredefFuncsProps = new Properties();
        try {
            PropertyLoader.fromResource(intPredefFuncsProps, IntegerTools.class, IntegerTools.IntegerPredefFunctionsPropertiesFile);
        }
        catch (Exception e) {
            throw new RuntimeException("could not load properties file \""+IntegerTools.IntegerPredefFunctionsPropertiesFile+"\", error was: "+e);
        }

        for(Object propKey : intPredefFuncsProps.keySet()) {
            String funcKey = (String)propKey;
            List<String> funcNameSignatureAndLevel = IntegerTools.splitAtColon(intPredefFuncsProps.getProperty(funcKey));
            String funcName = funcNameSignatureAndLevel.get(0);
            Pair<Integer,Integer> fixityAndPrecedence = null;
            if (funcNameSignatureAndLevel.size() > 2) {
                Integer fixity = IntegerTools.getFixityFromString(funcNameSignatureAndLevel.get(2));
                Integer precedence = Integer.parseInt(funcNameSignatureAndLevel.get(3).trim());
                fixityAndPrecedence = new Pair<Integer,Integer>(fixity,precedence);
            }
            List<String> args = new Vector<String>();
            Pair<List<String>, String> argSortsAndReturnSort = IntegerTools.splitUpSignature(funcNameSignatureAndLevel.get(1));
            for(String arg : argSortsAndReturnSort.x) {
                args.add(arg);
            }
            predefFuncsArgs.put(funcKey, new Triple<List<String>,String,Pair<Integer,Integer>>(args,argSortsAndReturnSort.y,fixityAndPrecedence));
            predefFuncsArgs.put(funcName, new Triple<List<String>,String,Pair<Integer,Integer>>(args,argSortsAndReturnSort.y,null)); // the rhs must not be infix
        }

        return predefFuncsArgs;
    }

    /** helper for getIntegerPredefFunctionSymbolNames, retrieves the fixity
     */
    private static int getFixityFromString(String fixityStr) {
        fixityStr = fixityStr.toLowerCase();
        fixityStr = fixityStr.trim();
        if (fixityStr.equals("infix")) {
            return SyntacticFunctionSymbol.INFIX;
        } else
        if (fixityStr.equals("infixl")) {
            return SyntacticFunctionSymbol.INFIXL;
        } else
        if (fixityStr.equals("infixr")) {
            return SyntacticFunctionSymbol.INFIXR;
        } else {
            throw new RuntimeException("could not determine fixity, argument was: \""+fixityStr+"\"");
        }
    }

    /** helper for getIntegerPredefFunctionSymbolNames, splits at a colon and returns the parts
     */
    private static List<String> splitAtColon(String str) {
        String[] parts = str.split(":");
        List<String> partsList = new Vector<String>();
        for(int i=0;i<parts.length;++i) {
            partsList.add(parts[i].trim());
        }
        return partsList;
    }

    /** helper for getIntegerPredefFunctionSymbolNames, returns the list of argument sorts and the return sort
     * as defined in the IntegerPredefFunctionsPropertiesFile
     */
    private static Pair<List<String>,String> splitUpSignature(String sigStr) {
        List<String> argList = new Vector<String>();
        String retSortName = sigStr.split("->")[1].trim();
        String[] parts = sigStr.split(",");
        for(int i=0;i<parts.length;++i) {
            int indexOfArrow = parts[i].indexOf("->");
            if (indexOfArrow > -1) {
                parts[i] = parts[i].substring(0,indexOfArrow);
            }
            argList.add(parts[i].trim());
        }
        return new Pair<List<String>,String>(argList,retSortName);
    }


}
