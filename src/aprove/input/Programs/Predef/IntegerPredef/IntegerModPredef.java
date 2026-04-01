package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerModPredef extends AbstractIntegerPredefItem {

    private static final String modName = "mod_int";

    public IntegerModPredef() {
        this(null, null, null, null, null);
    }

    /** creates an object which can build a Term mod(left, right)
     * @param nodeContent the content of the node, should be a "%"
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param left Term on the left side of the "%"-symbol
     * @param right Term on the right side of the "%"-symbol
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerModPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm left, AlgebraTerm right) {
        super(nodeContent, typeContext, program, Arrays.asList(left, right));
    }


    /** returns the mod symbol
     * if necessary, adds rules for minus to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return mod symbol from the program
     */
    public static DefFunctionSymbol getModSymbol(TypeContext typeContext, Program program) {
        IntegerModPredef imp = new IntegerModPredef(null, typeContext, program, null, null);
        return imp.getModSymbol();
    }


    /** returns the mod symbol
     * if necessary, adds rules for minus to program and the types to typeContext if they do not exist yet
     * @return mod symbol from the program
     */
    public DefFunctionSymbol getModSymbol() {
        DefFunctionSymbol modSym = this.program.getDefFunctionSymbol(IntegerModPredef.modName);
        if (modSym == null) {
            modSym = this.createModRules();
        }
        return modSym;
    }


    @Override
    public AlgebraTerm toTerm() {
        if (this.nodeContent.equals("%")) {
            DefFunctionSymbol modSym = this.getModSymbol();
            return AlgebraFunctionApplication.create(modSym, this.arguments);
        }
        return null;
    }



    /* creates the rules for modulo
     */
    private DefFunctionSymbol createModRules() {
        DefFunctionSymbol modSym = this.createAndAddDefFunSym(IntegerModPredef.modName, 2);

        // get the needed Function Symbols
        DefFunctionSymbol minusSym = IntegerMinusPredef.getMinusSymbol(this.typeContext, this.program);
        DefFunctionSymbol multSym = IntegerMultPredef.getMultSymbol(this.typeContext, this.program);
        DefFunctionSymbol quotSym = IntegerQuotPredef.getQuotSymbol(this.typeContext, this.program);

        List<SyntacticFunctionSymbol> SPList = Arrays.asList((SyntacticFunctionSymbol)this.getSucc(), this.getPred());

        // create rules (2 rules are used, so that mod(x,0) will not be matched)
        //    mod(x,s(y)) -> minus(x,mult(quot(x,s(y)),s(y)))
        //    mod(x,p(y)) -> minus(x,mult(quot(x,p(y)),p(y)))
        for(SyntacticFunctionSymbol sp : SPList) {
            AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
            AlgebraTerm spTerm = AlgebraFunctionApplication.create(sp, Arrays.asList(AlgebraVariable.create(VariableSymbol.create("y"))));
            AlgebraTerm modTerm = AlgebraFunctionApplication.create(modSym, Arrays.asList(xVar, spTerm));
            AlgebraTerm quotTerm = AlgebraFunctionApplication.create(quotSym, Arrays.asList(xVar, spTerm));
            AlgebraTerm multTerm = AlgebraFunctionApplication.create(multSym, Arrays.asList(quotTerm, spTerm));
            AlgebraTerm minusTerm = AlgebraFunctionApplication.create(minusSym, Arrays.asList(xVar, multTerm));
            this.program.addRule(modSym, Rule.create(modTerm, minusTerm));
        }

        return modSym;
    }


}
