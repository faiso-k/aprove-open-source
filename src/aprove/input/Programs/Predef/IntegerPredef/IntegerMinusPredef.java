package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerMinusPredef extends AbstractIntegerPredefItem {

    private static final String minusName = "minus_int";

    public IntegerMinusPredef() {
        this(null, null, null, null, null);
    }

    /** creates an object which can build a Term minus(left, right)
     * @param nodeContent the content of the node, should be a "-"
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param left Term on the left side of the "-"-symbol
     * @param right Term on the right side of the "-"-symbol
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerMinusPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm left, AlgebraTerm right) {
        super(nodeContent, typeContext, program, Arrays.asList(left, right));
    }



    /** returns the minus symbol
     * if necessary, adds rules for minus to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return minus symbol from the program
     */
    public static DefFunctionSymbol getMinusSymbol(TypeContext typeContext, Program program) {
        IntegerMinusPredef imp = new IntegerMinusPredef(null, typeContext, program, null, null);
        return imp.getMinusSymbol();
    }


    /** returns the minus symbol
     * if necessary, adds rules for minus to program and the types to typeContext if they do not exist yet
     * @return minus symbol from the program
     */
    public DefFunctionSymbol getMinusSymbol() {
        DefFunctionSymbol minusSym = this.program.getDefFunctionSymbol(IntegerMinusPredef.minusName);
        if (minusSym == null) {
            minusSym = this.createMinusRules();
        }
        return minusSym;
    }


    @Override
    public AlgebraTerm toTerm() {
        if (this.nodeContent.equals("-")) {
            return this.toMinusTerm();
        }
        return null;
    }



    /* creates a Term with minus-symbol as root-symbol
     * and left and right as arguments
     */
    private AlgebraTerm toMinusTerm() {
        DefFunctionSymbol minusSym = this.getMinusSymbol();
        return AlgebraFunctionApplication.create(minusSym, this.arguments);
    }



    /* creates rules for minus
     */
    private DefFunctionSymbol createMinusRules() {
        DefFunctionSymbol minusSym = this.createAndAddDefFunSym(IntegerMinusPredef.minusName, 2);

        // minus is 0-commutative, i.e.
        //    minus(minus(z,y),x) == minus(minus(z,x),y)
        // but not 1-commutative, i.e.
        //    minus(x,minus(y,z)) != minus(y,minus(x,z))
        minusSym.setJCommutativity(0,true);
        minusSym.setJCommutativity(1,false);

        DefFunctionSymbol negSym = IntegerNegPredef.getNegSymbol(this.typeContext, this.program);

        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));
        AlgebraTerm zeroTerm = AlgebraFunctionApplication.create(this.getZero());
        AlgebraTerm sx = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(xVar));
        AlgebraTerm sy = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(yVar));
        AlgebraTerm px = AlgebraFunctionApplication.create(this.getPred(), Arrays.asList(xVar));
        AlgebraTerm py = AlgebraFunctionApplication.create(this.getPred(), Arrays.asList(yVar));
        List<AlgebraTerm> minusArgs;
        AlgebraTerm left, right, negTerm;

        // minus(0, 0) -> 0
        minusArgs = Arrays.asList(zeroTerm, zeroTerm);
        this.program.addRule(minusSym, Rule.create(AlgebraFunctionApplication.create(minusSym, minusArgs), zeroTerm));

        // minus(s(x), 0) -> s(x)
        minusArgs = Arrays.asList(sx, zeroTerm);
        this.program.addRule(minusSym, Rule.create(AlgebraFunctionApplication.create(minusSym, minusArgs), sx));

        // minus(p(x), 0) -> p(x)
        minusArgs = Arrays.asList(px, zeroTerm);
        this.program.addRule(minusSym, Rule.create(AlgebraFunctionApplication.create(minusSym, minusArgs), px));


        // minus(0, s(y)) -> p(neg(y))
        minusArgs = Arrays.asList(zeroTerm, sy);
        left = AlgebraFunctionApplication.create(minusSym, minusArgs);
        negTerm = AlgebraFunctionApplication.create(negSym, Arrays.asList(yVar));
        right = AlgebraFunctionApplication.create(this.getPred(), Arrays.asList(negTerm));
        this.program.addRule(minusSym, Rule.create(left, right));

        // minus(0, p(y)) -> s(neg(y))
        minusArgs = Arrays.asList(zeroTerm, py);
        left = AlgebraFunctionApplication.create(minusSym, minusArgs);
        negTerm = AlgebraFunctionApplication.create(negSym, Arrays.asList(yVar));
        right = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(negTerm));
        this.program.addRule(minusSym, Rule.create(left, right));

        // create rules:
        //        minus(s(x),s(y)) -> minus(x,y)
        //        minus(s(x),p(y)) -> s(s(minus(x,y)))
        //        minus(p(x),s(y)) -> p(p(minus(x,y)))
        //        minus(p(x),p(y)) -> minus(x,y)

        List<SyntacticFunctionSymbol> SPList = Arrays.asList((SyntacticFunctionSymbol)this.getSucc(), this.getPred());
        for(SyntacticFunctionSymbol sp1 : SPList) {
            for(SyntacticFunctionSymbol sp2 : SPList) {
                this.program.addRule(minusSym, this.createMinusRecRule(minusSym, sp1, sp2));
            }
        }

        return minusSym;
    }




    /* creates recursive rules for minus of the form
     * minus(sp1(x), sp2(y)) -> [sp1^2](minus(x,y))
     * where sp1^2 is introduced if sp1 != sp2
    */
    private Rule createMinusRecRule(DefFunctionSymbol minusSym, SyntacticFunctionSymbol sp1, SyntacticFunctionSymbol sp2) {
        List<AlgebraTerm> minusLArgs = new Vector<AlgebraTerm>();
        List<AlgebraTerm> minusRArgs = new Vector<AlgebraTerm>();

        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));

        minusLArgs.add(AlgebraFunctionApplication.create(sp1, Arrays.asList(xVar)));
        minusLArgs.add(AlgebraFunctionApplication.create(sp2, Arrays.asList(yVar)));
        AlgebraTerm left = AlgebraFunctionApplication.create(minusSym, minusLArgs);

        minusRArgs.add(xVar);
        minusRArgs.add(yVar);
        AlgebraTerm right = (AlgebraFunctionApplication.create(minusSym, minusRArgs));

        if (!sp1.equals(sp2)) {
            right = AlgebraFunctionApplication.create(sp1, Arrays.asList(right));
            right = AlgebraFunctionApplication.create(sp1, Arrays.asList(right));
        }

        return Rule.create(left, right);
    }

}
