package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerLessEqPredef extends AbstractIntegerPredefItem {

    private static final String lessName = "less_int";
    private static final String lessEqName = "lessEq_int";

    public IntegerLessEqPredef() {
        this(null,null,null,null,null);
    }

    /** creates an object which can build a Term less(left, right) or lessEq(left, right)
     * @param nodeContent the content of the node, should be one of "<" or "<="
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param left Term on the left side of the "< / <="-symbol
     * @param right Term on the right side of the "< / <="-symbol
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerLessEqPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm left, AlgebraTerm right) {
        super(nodeContent, typeContext, program, Arrays.asList(left, right));
    }

    /** returns the less symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return less symbol from the program
     */
    public static DefFunctionSymbol getLessSymbol(TypeContext typeContext, Program program) {
        IntegerLessEqPredef ilp = new IntegerLessEqPredef("<", typeContext, program, null, null);
        return ilp.getLessSymbol();
    }

    /** returns the less symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @return less symbol from the program
     */
    public DefFunctionSymbol getLessSymbol() {
        DefFunctionSymbol lessSym = this.program.getDefFunctionSymbol(IntegerLessEqPredef.lessName);
        if (lessSym == null) {
            lessSym = this.createLessRules();
        }
        return lessSym;
    }


    /** returns the lessEq symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return lessEq symbol from the program
     */
    public static DefFunctionSymbol getLessEqSymbol(TypeContext typeContext, Program program) {
        IntegerLessEqPredef ilp = new IntegerLessEqPredef("<=", typeContext, program, null, null);
        return ilp.getLessEqSymbol();
    }

    /** returns the lessEq symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @return lessEq symbol from the program
     */
    public DefFunctionSymbol getLessEqSymbol() {
        DefFunctionSymbol lessEqSym = this.program.getDefFunctionSymbol(IntegerLessEqPredef.lessEqName);
        if (lessEqSym == null) {
            lessEqSym = this.createLessEqRules();
        }
        return lessEqSym;
    }


    @Override
    public AlgebraTerm toTerm() {
        if (this.nodeContent.equals("<")) {
            return this.toLessTerm();
        }
        else if (this.nodeContent.equals("<=")) {
            return this.toLessEqTerm();
        }
        return null;
    }


    // helpers per symbol

    private AlgebraTerm toLessTerm() {
        DefFunctionSymbol lessSym = this.getLessSymbol();
        return AlgebraFunctionApplication.create(lessSym, this.arguments);
    }


    private AlgebraTerm toLessEqTerm() {
        DefFunctionSymbol lessEqSym = this.getLessEqSymbol();
        return AlgebraFunctionApplication.create(lessEqSym, this.arguments);
    }




    // creation of rules

    /* creation of rules for the strict less
     * only the rule less(0,0) -> false has to be created here, the rest will be created in createLessEqRestRules()
     */
    private DefFunctionSymbol createLessRules() {
        AlgebraTerm boolType = this.typeContext.getTypeDef("bool").getDefTerm();
        Sort boolSort = this.program.getSort("bool");
        DefFunctionSymbol lessSym = this.createAndAddDefFunSym(IntegerLessEqPredef.lessName, 2, boolType, boolSort);

        ConstructorSymbol falseCon = this.program.getConstructorSymbol("false");
        AlgebraTerm falseTerm = AlgebraFunctionApplication.create(falseCon);

        // create Rule less(0, 0) -> false
        List<AlgebraTerm> lessArgs = new Vector<AlgebraTerm>();
        lessArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        lessArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        this.program.addRule(lessSym, Rule.create(AlgebraFunctionApplication.create(lessSym, lessArgs), falseTerm));

        // create the remaining rules
        this.createLessEqRestRules(lessSym);


        return lessSym;
    }


    /* creates rules for lessEq
     * only the rule lessEq(0,0) -> true is created here, the rest will be created in createLessEqRestRules()
     */
    private DefFunctionSymbol createLessEqRules() {
        AlgebraTerm boolType = this.typeContext.getTypeDef("bool").getDefTerm();
        Sort boolSort = this.program.getSort("bool");
        DefFunctionSymbol lessEqSym = this.createAndAddDefFunSym(IntegerLessEqPredef.lessEqName, 2, boolType, boolSort);

        ConstructorSymbol trueCon = this.program.getConstructorSymbol("true");
        AlgebraTerm trueTerm = AlgebraFunctionApplication.create(trueCon);

        // create Rule lessEq(0, 0) -> true
        List<AlgebraTerm> lessArgs = new Vector<AlgebraTerm>();
        lessArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        lessArgs.add(AlgebraFunctionApplication.create(this.getZero()));
        this.program.addRule(lessEqSym, Rule.create(AlgebraFunctionApplication.create(lessEqSym, lessArgs), trueTerm));

        // create the remaining rules
        this.createLessEqRestRules(lessEqSym);


        return lessEqSym;
    }


    /* creates the rules common to less and lessEq
     */
    private void createLessEqRestRules(DefFunctionSymbol lessSym) {
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
        List<AlgebraTerm> lessArgs;

        // create Rule less(0, s(y)) -> true
        lessArgs = Arrays.asList(zeroTerm, sy);
        left = AlgebraFunctionApplication.create(lessSym, lessArgs);
        this.program.addRule(lessSym, Rule.create(left, trueTerm));

        // create Rule less(s(x), 0) -> false
        lessArgs = Arrays.asList(sx, zeroTerm);
        left = AlgebraFunctionApplication.create(lessSym, lessArgs);
        this.program.addRule(lessSym, Rule.create(left, falseTerm));

        // create Rule less(0, p(y)) -> false
        lessArgs = Arrays.asList(zeroTerm, py);
        left = AlgebraFunctionApplication.create(lessSym, lessArgs);
        this.program.addRule(lessSym, Rule.create(left, falseTerm));

        // create Rule less(p(x), 0) -> true
        lessArgs = Arrays.asList(px, zeroTerm);
        left = AlgebraFunctionApplication.create(lessSym, lessArgs);
        this.program.addRule(lessSym, Rule.create(left, trueTerm));

        // create Rule less(p(x), s(y)) -> true
        lessArgs = Arrays.asList(px, sy);
        left = AlgebraFunctionApplication.create(lessSym, lessArgs);
        this.program.addRule(lessSym, Rule.create(left, trueTerm));

        // create Rule less(s(x), p(y)) -> false
        lessArgs = Arrays.asList(sx, py);
        left = AlgebraFunctionApplication.create(lessSym, lessArgs);
        this.program.addRule(lessSym, Rule.create(left, falseTerm));

        // create Rule less(s(x), s(y)) -> less(x,y)
        lessArgs = Arrays.asList(sx, sy);
        left = AlgebraFunctionApplication.create(lessSym, lessArgs);
        right = AlgebraFunctionApplication.create(lessSym, Arrays.asList(xVar, yVar));
        this.program.addRule(lessSym, Rule.create(left, right));

        // create Rule less(p(x), p(y)) -> less(x,y)
        lessArgs = Arrays.asList(px, py);
        left = AlgebraFunctionApplication.create(lessSym, lessArgs);
        right = AlgebraFunctionApplication.create(lessSym, Arrays.asList(xVar, yVar));
        this.program.addRule(lessSym, Rule.create(left, right));
    }

}
