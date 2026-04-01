package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerDataStructureCreator {

    private static final String intName  = AbstractIntegerPredefItem.getIntTypeName();
    private static final String zeroName = AbstractIntegerPredefItem.getZeroName();
    private static final String succName = AbstractIntegerPredefItem.getSuccName();
    private static final String predName = AbstractIntegerPredefItem.getPredName();

    private static final String succSelectorName = AbstractIntegerPredefItem.getSuccSelectorName();
    private static final String predSelectorName = AbstractIntegerPredefItem.getPredSelectorName();


    private TypeContext typeContext;
    private Program program;
    private AlgebraTerm intType;
    private Sort intSort;
    private ConstructorSymbol zero;
    private ConstructorSymbol succ;
    private ConstructorSymbol pred;

    public IntegerDataStructureCreator() {
        this(null, null);
    }

    /** creates an object capable of creating the Integer Data Structure and the rules for it
     * @param typeContext the Type Context the new Type Definition will be inserted into
     * @param program the program the new rules are to be inserted into
     * @param name the name of the Integer Data Structure (typically int)
     * @return the newly created Type Definition for Integer
     */
    public IntegerDataStructureCreator(TypeContext typeContext, Program program) {
        this.typeContext = typeContext;
        this.program = program;
        this.intType = null;
    }


    // Selectors

    public AlgebraTerm getIntType() {
        if (this.intType == null) {
            this.intType = this.typeContext.getTypeDef(IntegerDataStructureCreator.intName).getDefTerm();
        }
        return this.intType;
    }


    /** Creates the Integer Data Structure with zero, succ, and pred Function Symbols.
     *  The TypeDefinition and Sort are added to the typeContext and the program, respectively.
     *  Also created are equal and isa rules.
     * @return the newly created Type Definition
     */
    public TypeDefinition createIntegerDataStructure() {
        TypeDefinition intTD = this.createIntegerTypeDef();
        this.intSort = this.createIntegerSort();
        if (this.intSort == null) {
            return null;
        }
        this.createDataStructureSymbols(intTD);
        this.createPredefDataStructFunctions();
        return intTD;
    }


    /* creates the Integer Type Definition and adds it to the typeContext
    */
    private TypeDefinition createIntegerTypeDef() {
        TypeDefinition td = new TypeDefinition(TypeTools.getTypeCons(IntegerDataStructureCreator.intName,0));
        this.typeContext.addTypeDef(td);
        return td;
    }

    /* creates the Integer Sort
     */
    private Sort createIntegerSort() {
        // TODO is this the right way to add a sort?
        Sort s = Sort.create(IntegerDataStructureCreator.intName);
        try {
            this.program.addSort(s);
        }
        catch (ProgramException e) {
            return null;
        }
        return s;
    }

    /* creates the ConstructorSymbol zero and the DefFunctionSymbols succ, pred
     * and sets the types of zero, succ, and pred in the passed TypeDefinition
     */
    private void createDataStructureSymbols(TypeDefinition intTypeDef) {
        List<Sort> oneIntArgSorts = Arrays.asList(this.intSort);

        this.zero = ConstructorSymbol.create(IntegerDataStructureCreator.zeroName,new Vector<Sort>(0),this.intSort);
        this.succ = ConstructorSymbol.create(IntegerDataStructureCreator.succName,oneIntArgSorts,this.intSort);
        this.pred = ConstructorSymbol.create(IntegerDataStructureCreator.predName,oneIntArgSorts,this.intSort);

        AlgebraTerm tIntType = this.getIntType();
        intTypeDef.setSingleTypeOf(this.zero, new Type(tIntType));
        intTypeDef.setSingleTypeOf(this.succ, new Type(TypeTools.function(Arrays.asList(tIntType), tIntType)));
        intTypeDef.setSingleTypeOf(this.pred, new Type(TypeTools.function(Arrays.asList(tIntType), tIntType)));
        intTypeDef.setWitnessTerm(AlgebraFunctionApplication.create(this.zero));

        try {
            this.program.addConstructorSymbol(this.zero);
            this.program.addConstructorSymbol(this.succ);
            this.program.addConstructorSymbol(this.pred);
        } catch (ProgramException e) { }

        // zero has no selectors
        this.zero.setSelectors(new Vector<DefFunctionSymbol>());

        // create and set selectors for succ and pred
        DefFunctionSymbol succSelector = this.createSelector(IntegerDataStructureCreator.succSelectorName, this.succ, this.pred);
        this.succ.setSelectors(new Vector<DefFunctionSymbol>(Arrays.asList(succSelector)));
        DefFunctionSymbol predSelector = this.createSelector(IntegerDataStructureCreator.predSelectorName, this.pred, this.succ);
        this.pred.setSelectors(new Vector<DefFunctionSymbol>(Arrays.asList(predSelector)));

        this.intSort.addConstructorSymbol(this.zero);
        this.intSort.addConstructorSymbol(this.succ);
        this.intSort.addConstructorSymbol(this.pred);
    }




    /* creates a selector with the specified name for the ConstructorSymbol sp (should be one of succ or pred)
     * where nonSp is the respective other. For this, the rule sel(nonSp(x)) -> 0 will be created.
     * Furthermore the rule sel(0) -> 0 is created
     */
    private DefFunctionSymbol createSelector(String selName, SyntacticFunctionSymbol sp, SyntacticFunctionSymbol nonSp) {
        List<Sort> oneIntArgSorts = Arrays.asList(this.intSort);
        DefFunctionSymbol sel = DefFunctionSymbol.create(selName, oneIntArgSorts, this.intSort);

        List<AlgebraTerm> typeArgs = new Vector<AlgebraTerm>();
        typeArgs.add(this.getIntType());

        this.typeContext.setSingleTypeOf(sel, new Type(TypeTools.function(typeArgs, this.getIntType())));
        try {
            this.program.addDefFunctionSymbol(sel);
            this.program.setFunctionSignature(sel, Symbol.SELECTORSIG);
        } catch (ProgramException e) { throw new RuntimeException("A Function Symbol with name ''"+selName+"'' already exists."); }

        sel.setTermination(true);

        // create rule sel(sp(x)) -> x
        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm spTerm = AlgebraFunctionApplication.create(sp, Arrays.asList(xVar));
        AlgebraTerm selTerm = AlgebraFunctionApplication.create(sel,Arrays.asList(spTerm));
        this.program.addRule(sel, Rule.create(selTerm, xVar));


        /*
        // create rule sel(nonSp(x)) -> 0
        xVar = xVar.deepcopy();
        Term zeroTerm = FunctionApplication.create(this.zero);
        Term nonSpTerm = FunctionApplication.create(nonSp, Arrays.asList(xVar));
        selTerm = FunctionApplication.create(sel, Arrays.asList(nonSpTerm));
        this.program.addRule(sel, Rule.create(selTerm, zeroTerm));

        // create rule sel(0) -> 0
        zeroTerm = zeroTerm.deepcopy();
        selTerm = FunctionApplication.create(sel, Arrays.asList(zeroTerm));
        this.program.addRule(sel, Rule.create(selTerm, zeroTerm));
        */

        return sel;
    }




    /* creates rules for the Functions isa_zero, isa_succ, isa_pred, and equal_int
     */
    private void createPredefDataStructFunctions() {
        List<Sort> oneIntArgSorts = Arrays.asList(this.intSort);
        List<Sort> twoIntArgSorts = Arrays.asList(this.intSort, this.intSort);

        List<AlgebraTerm> oneIntArg = new Vector<AlgebraTerm>();
        oneIntArg.add(this.getIntType());

        List<AlgebraTerm> twoIntArg = new Vector<AlgebraTerm>();
        twoIntArg.add(this.getIntType());
        twoIntArg.add(this.getIntType());

        Sort boolSort = this.program.getSort("bool");
        AlgebraTerm boolType = this.typeContext.getTypeDef("bool").getDefTerm();

        DefFunctionSymbol eq_int = DefFunctionSymbol.create("equal_"+IntegerDataStructureCreator.intName, twoIntArgSorts, boolSort);
        eq_int.setTermination(true);
        eq_int.setJCommutativity(0,true);
        eq_int.setJCommutativity(1,true);
        this.typeContext.setSingleTypeOf(eq_int, new Type(TypeTools.function(twoIntArg, boolType)));
        this.intSort.setEqualOp(eq_int);

        try {
            this.program.addPredefFunctionSymbol(eq_int);
            this.program.setFunctionSignature(eq_int, Symbol.BOOLSIG);    // Symbol.BOOLSIG is also used in StructPass.java
        }
        catch (ProgramException e) { }


        // creating the rules for isa checks and equality
        Vector<SyntacticFunctionSymbol> funcs = new Vector<SyntacticFunctionSymbol>();
        funcs.add(this.zero);
        funcs.add(this.succ);
        funcs.add(this.pred);
        for(SyntacticFunctionSymbol fsym1 : funcs) {
            DefFunctionSymbol isa_fsym1 = DefFunctionSymbol.create("isa_"+fsym1.getName(), oneIntArgSorts, boolSort);
            isa_fsym1.setTermination(true);
            this.typeContext.setSingleTypeOf(isa_fsym1, new Type(TypeTools.function(oneIntArg, boolType)));
            try {
                this.program.addPredefFunctionSymbol(isa_fsym1);
                this.program.setFunctionSignature(isa_fsym1,Symbol.BOOLSIG); // Symbol.BOOLSIG is also used in StructPass.java
            } catch (ProgramException e) { }
            for(SyntacticFunctionSymbol fsym2 : funcs) {
                this.program.addRule(eq_int, this.createEqRule(eq_int, fsym1, fsym2));
                this.program.addRule(isa_fsym1, this.createIsaRule(isa_fsym1, fsym1, fsym2));
            }
        }
    }


    /* creates a rule isa_fsym1(fsym2(args2)) -> (true|false)
     */
    private Rule createIsaRule(DefFunctionSymbol isa_fsym1, SyntacticFunctionSymbol fsym1, SyntacticFunctionSymbol fsym2) {

        List<AlgebraTerm> args2 = new Vector<AlgebraTerm>();
        if (fsym2.getArity() > 0) {
            AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
            args2.add(xVar);
        }

        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(AlgebraFunctionApplication.create(fsym2, args2));

        TypeDefinition boolTD = this.typeContext.getTypeDef("bool");
        ConstructorSymbol trueSym=null, falseSym=null;
        for(Symbol sym : boolTD.getDeclaredSymbols()) {
            if (sym.getName().equals("true")) {
                trueSym = (ConstructorSymbol) sym;
            } else
                if (sym.getName().equals("false")) {
                    falseSym = (ConstructorSymbol) sym;
                }
        }

        AlgebraTerm isaResultTerm = AlgebraFunctionApplication.create( (fsym1.equals(fsym2)) ? trueSym : falseSym );

        return Rule.create(AlgebraFunctionApplication.create(isa_fsym1, args), isaResultTerm);
    }


    /* creates a rule eqsym( fsym1(args1), fsym2(args2) ) -> (true|false)
     */
    private Rule createEqRule(DefFunctionSymbol eqSym, SyntacticFunctionSymbol fsym1, SyntacticFunctionSymbol fsym2) {

        // counts the number of Terms with arguments (i.e. it ranges from 0 to 2)
        int numArgs=0;

        // the lists args1 and args2 only contain a variable and are used in case fsym1 or fsym2 are succ or pred
        AlgebraTerm x1Var = AlgebraVariable.create(VariableSymbol.create("x1"));
        AlgebraTerm x2Var = AlgebraVariable.create(VariableSymbol.create("x2"));

        List<AlgebraTerm> args1 = new Vector<AlgebraTerm>();
        if (fsym1.getArity()>0) {
            args1.add(x1Var);
            ++numArgs;
        }

        List<AlgebraTerm> args2 = new Vector<AlgebraTerm>();
        if(fsym2.getArity()>0) {
            args2.add(x2Var);
            ++numArgs;
        }

        TypeDefinition boolTD = this.typeContext.getTypeDef("bool");
        ConstructorSymbol trueSym=null, falseSym=null;
        for(Symbol sym : boolTD.getDeclaredSymbols()) {
            if (sym.getName().equals("true")) {
                trueSym = (ConstructorSymbol) sym;
            } else
                if (sym.getName().equals("false")) {
                    falseSym = (ConstructorSymbol) sym;
                }
        }

        AlgebraTerm eqResultTerm;

        boolean eqResult;
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();

        args.add(AlgebraFunctionApplication.create(fsym1, args1));
        args.add(AlgebraFunctionApplication.create(fsym2, args2));

        eqResult = fsym1.equals(fsym2);
        if ( (eqResult) && (numArgs == 2) ) {
            // in this case we have the same function symbol and both have a variable as argument => recursive call
            List<AlgebraTerm> argsRec = new Vector<AlgebraTerm>();
            argsRec.add(x1Var);
            argsRec.add(x2Var);
            eqResultTerm = AlgebraFunctionApplication.create(eqSym,argsRec);
        }
        else {
            eqResultTerm = AlgebraFunctionApplication.create( (eqResult) ? trueSym : falseSym );
        }

        return Rule.create(AlgebraFunctionApplication.create(eqSym, args), eqResultTerm);
    }


}
