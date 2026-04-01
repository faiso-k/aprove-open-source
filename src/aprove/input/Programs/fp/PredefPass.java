package aprove.input.Programs.fp;

import java.util.*;

import aprove.input.Generated.fp.node.*;
import aprove.input.Programs.Predef.*;
import aprove.input.Programs.Predef.IntegerPredef.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class PredefPass extends Pass {

    private String intName;

    @Override
    public void inStart(Start node) {
        this.containsInts = false;
        this.intName = AbstractIntegerPredefItem.getIntTypeName();
        PredefDataStructureSymbols.clear();
        PredefFunctionSymbols.clear();
        this.addPredefs();
    }

    @Override
    public void outStart(Start node) {
        if (this.containsInts) {
            this.addIntStruct();
        }
    }

    /** adds the predefined Data Structure for Integers with the name defined in intTypeName
     *  and the predefined functions (equal_int, isa_s_int, etc.)
     */
    private void addIntStruct() {
        String intTypeName = AbstractIntegerPredefItem.getIntTypeName();

        TypeDefinition intTD = (new IntegerDataStructureCreator(this.typeContext, this.prog)).createIntegerDataStructure();

        PredefDataStructureSymbols.addPredefinedSymbols(intTD);
        PredefFunctionSymbols.addPredefinedFunctions(IntegerTools.getIntegerPredefFunctions());

        this.sorttoken.put(intTypeName, new TId(intTypeName));
    }


    /** helper for addPredefs(), generates an entry which can be put into a map that is then
     * passed to PredefFunctionSymbols.addPredefinedFunctions
     */
    private Triple<List<String>,String,Pair<Integer,Integer>> genFuncTriple(DefFunctionSymbol defSym) {
        List<String> argSortsNames = new Vector<String>();
        for (Sort argSort : defSym.getArgSorts()) {
            argSortsNames.add(argSort.getName());
        }
        String retSortName = defSym.getSort().getName();

        Pair<Integer,Integer> fixityAndPrecedence = null;
        if (defSym.isInfix()) {
            Integer fixity = Integer.valueOf(defSym.getFixity());
            Integer precedence = Integer.valueOf(defSym.getFixityLevel());
            fixityAndPrecedence = new Pair<Integer,Integer>(fixity, precedence);
        }

        return new Triple<List<String>,String,Pair<Integer,Integer>>(argSortsNames, retSortName, fixityAndPrecedence);
    }


    /** adds the predefined functions that are already in the program when this Pass is called
     */
    private void addPredefs() {
        Map<String, Triple<List<String>,String,Pair<Integer,Integer>>> predefFuncs = new HashMap<String, Triple<List<String>,String,Pair<Integer,Integer>>>();

        predefFuncs.put("||", this.genFuncTriple(this.prog.getPredefFunctionSymbol("or")));
        predefFuncs.put("&&", this.genFuncTriple(this.prog.getPredefFunctionSymbol("and")));

        for(Sort s : this.prog.getSorts()) {
            predefFuncs.put("==", this.genFuncTriple(this.prog.getPredefFunctionSymbol("equal_"+s.getName())));
        }

        for(ConstructorSymbol consSym : this.prog.getConstructorSymbols()) {
            PredefDataStructureSymbols.addPredefinedSymbol(consSym);
        }

        for(DefFunctionSymbol defSym : this.prog.getDefFunctionSymbols()) {
            predefFuncs.put(defSym.getName(), this.genFuncTriple(defSym));
        }
        PredefFunctionSymbols.addPredefinedFunctions(predefFuncs);
    }


    /** checks whether the passed tokens content is equal to the name
     * integers are assumed to have and sets containsInts accordingly
     */
    private void testForInt(Node node) {
        String sortName = this.chop(node);
        if (this.intName.equals(sortName)) {
            this.containsInts = true;
        }
    }

    @Override
    public void inASelidlist(ASelidlist node) {
        this.testForInt(node.getSort());
    }

    @Override
    public void inASelidcomma(ASelidcomma node) {
        this.testForInt(node.getSort());
    }

    @Override
    public void inAIdlist(AIdlist node) {
        this.testForInt(node.getId());
    }

    @Override
    public void inAIdcomma(AIdcomma node) {
        this.testForInt(node.getId());
    }

    @Override
    public void inAFunct(AFunct node) {
        this.testForInt(node.getReturn());
    }

    @Override
    public void inAOpdef(AOpdef node) {
        this.testForInt(node.getReturn());
    }


}
