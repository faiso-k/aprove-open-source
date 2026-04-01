package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;


public class IntegerMultPredef extends AbstractIntegerPredefItem {

    private static final String multName = "mult_int";

    public IntegerMultPredef() {
        this(null, null, null, null, null);
    }

    /** creates an object which can build a Term mult(left, right)
     * @param nodeContent the content of the node, should be a "*"
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param left Term on the left side of the "*"-symbol
     * @param right Term on the right side of the "*"-symbol
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerMultPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm left, AlgebraTerm right) {
        super(nodeContent, typeContext, program, Arrays.asList(left, right));
    }



    /** returns the mult symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return mult symbol from the program
     */
    public static DefFunctionSymbol getMultSymbol(TypeContext typeContext, Program program) {
        IntegerMultPredef imp = new IntegerMultPredef(null, typeContext, program, null, null);
        return imp.getMultSymbol();
    }


    /** returns the mult symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @return mult symbol from the program
     */
    public DefFunctionSymbol getMultSymbol() {
        DefFunctionSymbol multSym = this.program.getDefFunctionSymbol(IntegerMultPredef.multName);
        if (multSym == null) {
            multSym = this.createMultRules();
        }
        return multSym;
    }


    /** returns a Term representing the String
     */
    @Override
    public AlgebraTerm toTerm() {
        if (this.nodeContent.equals("*")) {
            return this.toMultTerm();
        }
        return null;
    }



    /* creates a term with a mult symbol as root and with the two arguments which were passed as left and right
     */
    private AlgebraTerm toMultTerm() {
        DefFunctionSymbol multSym = this.getMultSymbol();
        return AlgebraFunctionApplication.create(multSym, this.getArguments());
    }



    /* creates the rules for mult
     */
    private DefFunctionSymbol createMultRules() {
        DefFunctionSymbol multSym = this.createAndAddDefFunSym(IntegerMultPredef.multName, 2);

        // setting commutativity of mult
        multSym.setJCommutativity(0,true);
        multSym.setJCommutativity(1,true);

        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));
        List<AlgebraTerm> multArgs = new Vector<AlgebraTerm>();

        // mult(0, y) -> 0
        multArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        multArgs.add(yVar);
        this.program.addRule(multSym, Rule.create(AlgebraFunctionApplication.create(multSym, multArgs), AlgebraFunctionApplication.create(this.getZero())));


        // get the plus and minus symbols
        DefFunctionSymbol plusSym = IntegerPlusPredef.getPlusSymbol(this.getTypeContext(), this.getProgram());
        DefFunctionSymbol minusSym = IntegerMinusPredef.getMinusSymbol(this.getTypeContext(), this.getProgram());


        // create rules:
        //     mult(s(x),y) -> plus(mult(x,y))
        //     mult(p(x),y) -> minus(mult(x,y))
        this.program.addRule(multSym, this.createMultRecRule(multSym, this.getSucc(), plusSym));
        this.program.addRule(multSym, this.createMultRecRule(multSym, this.getPred(), minusSym));

        return multSym;
    }



    /* Helper for createMultRules()
     * creates recursive rules of the form mult(sp(x),y) -> plusminus(mult(x,y), y),
     * i.e. should be called with pairs succ/plus and pred/minus
     */
    private Rule createMultRecRule(DefFunctionSymbol mult, SyntacticFunctionSymbol sp, DefFunctionSymbol plusminus) {
        List<AlgebraTerm> multLArgs = new Vector<AlgebraTerm>();
        List<AlgebraTerm> multRArgs = new Vector<AlgebraTerm>();
        List<AlgebraTerm> spLArgs = new Vector<AlgebraTerm>();
        List<AlgebraTerm> plusminusRArgs = new Vector<AlgebraTerm>();

        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));

        spLArgs.add(xVar);
        multLArgs.add(AlgebraFunctionApplication.create(sp, spLArgs));
        multLArgs.add(yVar);

        multRArgs.add(xVar);
        multRArgs.add(yVar);
        plusminusRArgs.add(AlgebraFunctionApplication.create(mult, multRArgs));
        plusminusRArgs.add(yVar);

        return Rule.create(AlgebraFunctionApplication.create(mult, multLArgs), AlgebraFunctionApplication.create(plusminus, plusminusRArgs));
    }

}

