package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerGreaterEqPredef extends AbstractIntegerPredefItem {

    private static String greaterName = "greater_int";
    private static String greaterEqName = "greaterEq_int";

    public IntegerGreaterEqPredef() {
        this(null, null, null, null, null);
    }

    /** creates an object which can build a Term greater(left, right) or greaterEq(left, right)
     * @param nodeContent the content of the node, should be one of ">" or ">="
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param left Term on the left side of the "> / >="-symbol
     * @param right Term on the right side of the "> / >="-symbol
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerGreaterEqPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm left, AlgebraTerm right) {
        super(nodeContent, typeContext, program, Arrays.asList(left, right));
    }



    /** returns the greater symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return greater symbol from the program
     */
    public static DefFunctionSymbol getGreaterSymbol(TypeContext typeContext, Program program) {
        IntegerGreaterEqPredef igp = new IntegerGreaterEqPredef(">", typeContext, program, null, null);
        return igp.getGreaterSymbol();
    }

    /** returns the greater symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @return greater symbol from the program
     */
    public DefFunctionSymbol getGreaterSymbol() {
        DefFunctionSymbol greaterSym = this.program.getDefFunctionSymbol(IntegerGreaterEqPredef.greaterName);
        if (greaterSym == null) {
            greaterSym = this.createGreaterRules();
        }
        return greaterSym;
    }


    /** returns the greaterEq symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return greaterEq symbol from the program
     */
    public static DefFunctionSymbol getGreaterEqSymbol(TypeContext typeContext, Program program) {
        IntegerGreaterEqPredef igp = new IntegerGreaterEqPredef(">=", typeContext, program, null, null);
        return igp.getGreaterEqSymbol();
    }

    /** returns the greaterEq symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @return greaterEq symbol from the program
     */
    public DefFunctionSymbol getGreaterEqSymbol() {
        DefFunctionSymbol greaterEqSym = this.program.getDefFunctionSymbol(IntegerGreaterEqPredef.greaterEqName);
        if (greaterEqSym == null) {
            greaterEqSym = this.createGreaterEqRules();
        }
        return greaterEqSym;
    }



    @Override
    public AlgebraTerm toTerm() {
        if (this.nodeContent.equals(">")) {
            return this.toGreaterTerm();
        }
        else if (this.nodeContent.equals(">=")) {
            return this.toGreaterEqTerm();
        }
        return null;
    }


    // helpers per symbol

    private AlgebraTerm toGreaterTerm() {
        DefFunctionSymbol greaterSym = this.getGreaterSymbol();
        return AlgebraFunctionApplication.create(greaterSym, this.arguments);
    }


    private AlgebraTerm toGreaterEqTerm() {
        DefFunctionSymbol greaterEqSym = this.getGreaterEqSymbol();
        return AlgebraFunctionApplication.create(greaterEqSym, this.arguments);
    }






    // creation of rules

    /* creation of rules for the strict greater
     * only the rule greater(0,0) -> false has to be created here, the rest will be created in createGreaterEqRestRules()
     */
    private DefFunctionSymbol createGreaterRules() {
        AlgebraTerm boolType = this.typeContext.getTypeDef("bool").getDefTerm();
        Sort boolSort = this.program.getSort("bool");
        DefFunctionSymbol greaterSym = this.createAndAddDefFunSym(IntegerGreaterEqPredef.greaterName, 2, boolType, boolSort);

        ConstructorSymbol falseCon = this.program.getConstructorSymbol("false");
        AlgebraTerm falseTerm = AlgebraFunctionApplication.create(falseCon);

        // create Rule greater(0, 0) -> false
        List<AlgebraTerm> greaterArgs = new Vector<AlgebraTerm>();
        greaterArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        greaterArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        this.program.addRule(greaterSym, Rule.create(AlgebraFunctionApplication.create(greaterSym, greaterArgs), falseTerm));

        // create the remaining rules
        this.createGreaterEqRestRules(greaterSym);


        return greaterSym;
    }


    /* creates rules for greaterEq
     * only the rule greaterEq(0,0) -> true is created here, the rest will be created in createGreaterEqRestRules()
     */
    private DefFunctionSymbol createGreaterEqRules() {
        AlgebraTerm boolType = this.typeContext.getTypeDef("bool").getDefTerm();
        Sort boolSort = this.program.getSort("bool");
        DefFunctionSymbol greaterEqSym = this.createAndAddDefFunSym(IntegerGreaterEqPredef.greaterEqName, 2, boolType, boolSort);

        ConstructorSymbol trueCon = this.program.getConstructorSymbol("true");
        AlgebraTerm trueTerm = AlgebraFunctionApplication.create(trueCon);

        // create Rule greaterEq(0, 0) -> true
        List<AlgebraTerm> greaterArgs = new Vector<AlgebraTerm>();
        greaterArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        greaterArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        this.program.addRule(greaterEqSym, Rule.create(AlgebraFunctionApplication.create(greaterEqSym, greaterArgs), trueTerm));

        // create the remaining rules
        this.createGreaterEqRestRules(greaterEqSym);


        return greaterEqSym;
    }


    /* creates the rules common to greater rand greaterEq
     */
    private void createGreaterEqRestRules(DefFunctionSymbol greaterSym) {
        ConstructorSymbol trueCon = this.program.getConstructorSymbol("true");
        ConstructorSymbol falseCon = this.program.getConstructorSymbol("false");

        AlgebraTerm trueTerm = AlgebraFunctionApplication.create(trueCon);
        AlgebraTerm falseTerm = AlgebraFunctionApplication.create(falseCon);
        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));
        AlgebraTerm zeroTerm = AlgebraFunctionApplication.create(this.getZero());
        AlgebraTerm sx = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(xVar));
        AlgebraTerm sy = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(yVar));
        AlgebraTerm px = AlgebraFunctionApplication.create(this.getPred(), Arrays.asList(xVar));
        AlgebraTerm py = AlgebraFunctionApplication.create(this.getPred(), Arrays.asList(yVar));

        AlgebraTerm left,right;
        List<AlgebraTerm> greaterArgs;

        // create Rule greater(0, s(y)) -> false
        greaterArgs = Arrays.asList(zeroTerm, sy);
        left = AlgebraFunctionApplication.create(greaterSym, greaterArgs);
        this.program.addRule(greaterSym, Rule.create(left, falseTerm));

        // create Rule greater(s(x), 0) -> true
        greaterArgs = Arrays.asList(sx, zeroTerm);
        left = AlgebraFunctionApplication.create(greaterSym, greaterArgs);
        this.program.addRule(greaterSym, Rule.create(left, trueTerm));

        // create Rule greater(0, p(y)) -> true
        greaterArgs = Arrays.asList(zeroTerm, py);
        left = AlgebraFunctionApplication.create(greaterSym, greaterArgs);
        this.program.addRule(greaterSym, Rule.create(left, trueTerm));

        // create Rule greater(p(x), 0) -> false
        greaterArgs = Arrays.asList(px, zeroTerm);
        left = AlgebraFunctionApplication.create(greaterSym, greaterArgs);
        this.program.addRule(greaterSym, Rule.create(left, falseTerm));

        // create Rule greater(p(x), s(y)) -> false
        greaterArgs = Arrays.asList(px, sy);
        left = AlgebraFunctionApplication.create(greaterSym, greaterArgs);
        this.program.addRule(greaterSym, Rule.create(left, falseTerm));

        // create Rule greater(s(x), p(y)) -> true
        greaterArgs = Arrays.asList(sx, py);
        left = AlgebraFunctionApplication.create(greaterSym, greaterArgs);
        this.program.addRule(greaterSym, Rule.create(left, trueTerm));

        // create Rule greater(s(x), s(y)) -> greater(x,y)
        greaterArgs = Arrays.asList(sx, sy);
        left = AlgebraFunctionApplication.create(greaterSym, greaterArgs);
        right = AlgebraFunctionApplication.create(greaterSym, Arrays.asList(xVar, yVar));
        this.program.addRule(greaterSym, Rule.create(left, right));

        // create Rule greater(p(x), p(y)) -> greater(x,y)
        greaterArgs = Arrays.asList(px, py);
        left = AlgebraFunctionApplication.create(greaterSym, greaterArgs);
        right = AlgebraFunctionApplication.create(greaterSym, Arrays.asList(xVar, yVar));
        this.program.addRule(greaterSym, Rule.create(left, right));
    }

}
