package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerAbsPredef extends AbstractIntegerPredefItem {

    private static final String absName = "abs_int";

    public IntegerAbsPredef() {
        this(null, null, null, null);
    }

    /** creates an object which can build a Term abs(negTerm)
     * @param nodeContent the content of the node, should be "abs"
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param absTerm Term following the "abs"-symbol
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerAbsPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm absTerm) {
        super(nodeContent, typeContext, program, Arrays.asList(absTerm));
    }


    /** returns the abs symbol
     * if necessary adds rules for abs to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return abs symbol from the program
     */
    public static DefFunctionSymbol getAbsSymbol(TypeContext typeContext, Program program) {
        IntegerAbsPredef iap = new IntegerAbsPredef(null, typeContext, program, null);
        return iap.getAbsSymbol();
    }

    /** returns the abs symbol
     * if necessary adds rules for abs to program and the types to typeContext if they do not exist yet
     * @return abs symbol from the program
     */
    public DefFunctionSymbol getAbsSymbol() {
        DefFunctionSymbol absSym = this.program.getDefFunctionSymbol(IntegerAbsPredef.absName);
        if (absSym == null) {
            absSym = this.createAbsRules();
        }
        return absSym;
    }


    public AlgebraTerm getAbsTerm() {
        return this.arguments.get(0);
    }




    /* creates the term abs(absTerm), where absTerm has been passed in constructor
     */
    @Override
    public AlgebraTerm toTerm() {
        DefFunctionSymbol absSym = this.getAbsSymbol();
        return AlgebraFunctionApplication.create(absSym, this.arguments);
    }



    /* creates the rules for the abs symbol
     */
    private DefFunctionSymbol createAbsRules() {
        DefFunctionSymbol absSym = this.createAndAddDefFunSym(IntegerAbsPredef.absName, 1);


        List<AlgebraTerm> absArgs;

        // abs(0) -> 0
        AlgebraTerm zeroTerm = AlgebraFunctionApplication.create(this.getZero());
        absArgs = Arrays.asList(zeroTerm);
        this.program.addRule(absSym, Rule.create(AlgebraFunctionApplication.create(absSym, absArgs), zeroTerm));

        // abs(s(x)) -> s(x)
        AlgebraTerm sx = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(AlgebraVariable.create(VariableSymbol.create("x"))));
        absArgs = Arrays.asList(sx);
        this.program.addRule(absSym, Rule.create(AlgebraFunctionApplication.create(absSym, absArgs), sx));

        // abs(p(x)) -> s(abs(x))
        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm px = AlgebraFunctionApplication.create(this.getPred(), Arrays.asList(xVar));
        absArgs = Arrays.asList(px);
        List<AlgebraTerm> sArgs = Arrays.asList((AlgebraTerm)AlgebraFunctionApplication.create(absSym, Arrays.asList(xVar)));
        this.program.addRule(absSym, Rule.create(AlgebraFunctionApplication.create(absSym, absArgs), AlgebraFunctionApplication.create(this.getSucc(), sArgs)));

        return absSym;
    }

}
