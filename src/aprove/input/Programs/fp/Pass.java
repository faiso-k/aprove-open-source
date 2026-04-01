package aprove.input.Programs.fp;

import java.math.*;
import java.util.*;

import aprove.input.Generated.fp.analysis.*;
import aprove.input.Generated.fp.node.*;
import aprove.input.Programs.Predef.IntegerPredef.*;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** Base class for the three passes of the FP parser.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

abstract class Pass extends DepthFirstAdapter {

    // magic sort, used when actual sort is yet to be determined
    private static final String FP_UNKNOWN_SORT_NAME = "FP_UNKONWN_SORT";
    protected static final Sort FP_UNKNOWN_SORT = Sort.create(Pass.FP_UNKNOWN_SORT_NAME);

    // names of the boolean functions && and ||
    protected static final String AND_NAME = "and";
    protected static final String OR_NAME = "or";


    protected Program prog;
    protected TypeContext typeContext;
    protected ParseErrors errors;
    // A hashtable containing sorts and the corresponding tokens.
    protected Hashtable sorttoken;
    // A set to collect all used names.
    protected Set<String> usedNames;

    // counting the occurences of a constructor/function in different definitions
    protected Map<String, Integer> consSymCounts;
    protected Map<String, Integer> funcSymCounts;

    // the return sorts names for every constructor name which is used more than once
    protected Map<String, Set<Pair<String,List<String>>>> consSymSignatures;

    // list of argument sorts names and the indication which sorts are always the same for every function with that name
    protected Map<String, Pair<Set<Pair<List<String>,String>>,BigInteger>> funcSymSignatureFixed;

    // assignment of operators to their fixity and precedence, e.g. "+" -> (INFIXL, 6)
    protected Map<String, Pair<Integer,Integer>> operatorFixity;

    // whether the FP-program contains integers
    protected boolean containsInts;

    protected String chop(Node node) {
    return node.toString().trim();
    }

    public Pass set(Pass pass) {
    this.setErrors(pass.getErrors());
    this.setProgram(pass.getProgram());
    this.setSorttoken(pass.getSorttoken());
    this.setUsedNames(pass.getUsedNames());
    this.setTypeContext(pass.getTypeContext());
    this.containsInts = pass.containsInts;
    this.consSymCounts = pass.consSymCounts;
    this.funcSymCounts = pass.funcSymCounts;
    this.funcSymSignatureFixed = pass.funcSymSignatureFixed;
    this.consSymSignatures = pass.consSymSignatures;
    this.operatorFixity = pass.operatorFixity;
    return this;
    }

    public Program getProgram() {
    return this.prog;
    }

    public void setProgram(Program prog) {
    this.prog = prog;
    }

    public Hashtable getSorttoken() {
    return this.sorttoken;
    }

    public void setTypeContext(TypeContext typeContext){
       this.typeContext = typeContext;
    }

    public TypeContext getTypeContext(){
       return this.typeContext;
    }

    public void setSorttoken(Hashtable s) {
    this.sorttoken = s;
    }

    public Set<String> getUsedNames() {
    return this.usedNames;
    }

    public void setUsedNames(Set<String> u) {
    this.usedNames = u;
    }



    protected void redeclaration(Token t) {
    this.addParseError(t, "redeclaration of symbol '"+this.chop(t)+"'");
    }

    protected AlgebraTerm getDeclaredType(String name,Token t) {
    AlgebraTerm ty = this.typeContext.getTypeDef(name).getDefTerm();
    if (ty == null){
        this.addParseError(t, "undeclared type '"+this.chop(t)+"'");
    }
    return ty;
    }

    protected boolean checkType(AlgebraTerm s1, AlgebraTerm s2, Token t) {
    if (!s1.equals(s2)) {
        this.addParseError(t, "type '"+s1.toString()+"' expected, not '"+ s2.toString()+"'");
        return false;
    }
    return true;
    }

    protected boolean checkdeclared(Sort s, Token t) {
    if (s == null) {
        this.addParseError(t, "undeclared sort '"+this.chop(t)+"'");
        return false;
    }
    return true;
    }
    protected boolean checksorts(Sort s1, Sort s2, Token t) {
        // if either one is FP_UNKNOWN_SORT, then there is no conflict
        if (s1.equals(Pass.FP_UNKNOWN_SORT) || s2.equals(Pass.FP_UNKNOWN_SORT)) {
            return true;
        }

    if (s1 != s2) {
        this.addParseError(t, "sort '"+s1.getName()+"' expected, not '"+ s2.getName()+"'");
        return false;
    }
    return true;
    }
    protected boolean checkdefsymbol(PLterm p, SyntacticFunctionSymbol f) {
    Token t = null;
    if (p instanceof AFunctAppLterm) {t = ((AFunctAppLterm)p).getId();}
    if (p instanceof AConstVarLterm) {t = ((AConstVarLterm)p).getId();}
    if (this.prog.getFunctionSymbol(this.chop(t)) != f) {
        this.addParseError(t, "function '"+f.getName()+"' expected");
        return false;
    }
    return true;
    }

    public void setErrors(ParseErrors errs) {
    this.errors = errs;
    }

    public ParseErrors getErrors() {
    return this.errors;
    }

    public void addParseError(Token t, int level, String msg) {
    ParseError pe = new ParseError(level);
    pe.setToken(this.chop(t));
    pe.setPosition(t.getLine(), t.getPos());
    pe.setMessage(msg);
    this.errors.add(pe);
    }

    public void addParseError(Token t, String msg) {
    this.addParseError(t, ParseError.ERROR, msg);
    }


    /** checks whether the passed string is an overloaded constructor
     * @param basename name to check
     * @return true iff the basename is an overloaded constructor
     */
    protected boolean isOverloadedConstructor(String basename) {
        if (this.consSymCounts.get(basename) != null) {
            if (this.consSymCounts.get(basename).intValue() > 1) {
                return true;
            }
            if ( (this.containsInts) && (IntegerPredefItem.isIntegerString(basename)) ) {
                return true;
            }
        }
        return false;
    }

    /** checks whether the passed string is an overloaded function
     * @param basename name to check
     * @return true iff the basename is an overloaded function
     */

    protected boolean isOverloadedFunction(String basename) {
        if (this.funcSymCounts.get(basename) != null) {
            if (this.funcSymCounts.get(basename).intValue() > 1) {
                return true;
            }
            if ( (this.containsInts) && (IntegerPredefItem.isIntegerString(basename)) ) {
                return true;
            }
        }
        return false;
    }

    /** creates a new name for a function that is overloaded (unless it is named "==")
     * @param basename the original name of the function
     * @param argSortsNames the names of the sorts of the arguments
     * @return a new name, which is constructed as basename'_'argSortsNames
     */
    protected String getNewFunctName(String basename, List<String> argSortsNames) {

        // handling of "==" is done later
        if (basename.equals("==")) {
            return null;
        }

        String newFunctName = basename;

        if (this.isOverloadedFunction(basename)) {
            // only create new name if the function name occurs more than once
            newFunctName += "_";
            boolean first = true;
            for(String argSortName : argSortsNames) {
                if (!first) {
                    newFunctName += ".";
                } else {
                    first = false;
                }
                newFunctName += argSortName;
            }
        }
        else {
            // if there is no need to create a new name, return null
            newFunctName = null;
        }

        return newFunctName;
    }


    /** creates a new name for a constructor that has been defined for multiple structures
     * @param basename original name of the constructor
     * @param retSortName name of the current structure
     * @return a new name, constructed as basename'_'retSortName
     */
    protected String getNewConsName(String basename, String retSortName) {
        if (this.isOverloadedConstructor(basename)) {
            return basename+"_"+retSortName;
        }
        else {
            // if there is no need to create a new name, return null
            return null;
        }
    }


    /** retrieves the set of argument sorts that could possibly occur
     * at argument position i of the function with the name functName
     * @param functName name of a function, contained in funcSymSignatureFixed
     * @param i argument position
     * @return set of possible argument sorts for position i, will be null if functName is not in funcSymSignatureFixed or i is not a valid position for functName
     */
    protected Set<String> getPossibleArgSortsAt(String functName, int i) {
        Set<String> possibleArgSorts = new HashSet<String>();
        Pair<Set<Pair<List<String>,String>>,BigInteger> funcSymSigsAndFixed = this.funcSymSignatureFixed.get(functName);

        // functName is not contained
        if(funcSymSigsAndFixed == null) {
            return null;
        }

        Set<Pair<List<String>,String>> funcSymSigs = funcSymSigsAndFixed.x;

        // if the requested position is fixed, the entry in the first argument sorts list will do
        if(funcSymSigsAndFixed.y.testBit(i)) {
            List<String> someArgSorts = funcSymSigs.iterator().next().x;
            if (i < someArgSorts.size()) {
                possibleArgSorts.add(someArgSorts.get(i));
            } else {
                return null;
            }
        }

        // otherwise iterate over all possible argument sorts
        else {
            for(Pair<List<String>,String> funcSymSig : funcSymSigs) {
                List<String> argSorts = funcSymSig.x;
                if (i < argSorts.size()) {
                    possibleArgSorts.add(argSorts.get(i));
                } else {
                    return null;
                }
            }
        }

        return possibleArgSorts;
    }


    /** returns the arguments sorts names, for which there actually is a function applicable
     * @param functName name of a (possibly overloaded) function
     * @param maybeArgSortsNames list of possible names of argument sorts
     * @return possible argument sorts names lists
     */
    protected List<Set<String>> getFunctPossibleArgsSortsNames(String functName, List<Set<String>> maybeArgSortsNames) {
        List<Set<String>> possibleArgSortsNames = new Vector<Set<String>>();

        // initializing data structure
        for(int i=0; i<maybeArgSortsNames.size(); ++i) {
            possibleArgSortsNames.add(new HashSet<String>());
        }

        Pair<Set<Pair<List<String>,String>>,BigInteger> funcSymSigsAndFixed = this.funcSymSignatureFixed.get(functName);
        Set<Pair<List<String>,String>> funcSymSigs = funcSymSigsAndFixed.x;

        for (Pair<List<String>,String> funcSymSig : funcSymSigs) {

            if (funcSymSig.x.size() != possibleArgSortsNames.size())
             {
                continue; // do not look at function signatures with different sizes
            }

            boolean contained = true;
            for(int i=0; i<funcSymSig.x.size(); ++i) {
                String argName = funcSymSig.x.get(i);
                if (!maybeArgSortsNames.get(i).contains(argName)) {
                    contained = false;
                    break;
                }
            }
            if (contained) {
                for(int i=0; i<funcSymSig.x.size(); ++i) {
                    possibleArgSortsNames.get(i).add(funcSymSig.x.get(i));
                }
            }
        }
        return possibleArgSortsNames;
    }


    /** retrieves some argument sorts names, useful for error handling
     * @param maybeArgSortsNames a list of possible argument sorts names
     * @return some arguments sorts names
     */
    protected List<String> getFirstArgsSortsNames(List<Set<String>> maybeArgSortsNames) {
        List<String> someArgSortsNames = new Vector<String>();
        for (Set<String> argSortsNames : maybeArgSortsNames) {
            someArgSortsNames.add(argSortsNames.iterator().next());
        }
        return someArgSortsNames;
    }



    /** returns the name of the sort the function with name functName has (might be overloaded)
     * @param functName name of the function to get the return sorts name of
     * @param argSortsNames list of argument sorts names
     * @return return sort of that function or null if no such function was found
     */
    protected String getFunctSymRetSortName(String functName, List<String> argSortsNames) {
        Pair<Set<Pair<List<String>,String>>,BigInteger> funcSymSigsAndFixed = this.funcSymSignatureFixed.get(functName);

        Set<Pair<List<String>,String>> funcSymSigs = funcSymSigsAndFixed.x;

        for (Pair<List<String>,String> funcSymSig : funcSymSigs) {
            if (argSortsNames.equals(funcSymSig.x)) {
                return funcSymSig.y;
            }
        }

        return null;
    }

    /** get the possible return sorts for a constructor
     * @param consName name of the constructor
     * @return set of possible return sorts, this constructor can have
     */
    protected Set<String> getConsPossibleRetSortsNames(String consName) {
        Set<String> possibleRetSortNames = new HashSet<String>();
        Set<Pair<String, List<String>>> consSymSigs = this.consSymSignatures.get(consName);
        for(Pair<String, List<String>> consSymSig : consSymSigs) {
            possibleRetSortNames.add(consSymSig.x);
        }
        if ( (this.containsInts) && (IntegerPredefItem.isIntegerString(consName)) ) {
            possibleRetSortNames.add(AbstractIntegerPredefItem.getIntTypeName());
        }
        return possibleRetSortNames;
    }

    /** get the argument sorts of a constructor, based on the return sort of it in case it is overloaded
     * @param consName name of the constructor (must not be a renamed constructor)
     * @param retSortName return sort's name, which will be look at in case the constructor is overloaded
     * @return argument sorts names
     */
    protected List<String> getConsArgSortsNames(String consName, String retSortName) {
        Set<Pair<String, List<String>>> consSymSigs = this.consSymSignatures.get(consName);
        for(Pair<String, List<String>> consSymSig : consSymSigs) {
            if (retSortName.equals(consSymSig.x)) {
                return consSymSig.y;
            }
        }
        return null;
    }
}
