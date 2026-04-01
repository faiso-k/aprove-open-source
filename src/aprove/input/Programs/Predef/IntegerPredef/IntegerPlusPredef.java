package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerPlusPredef extends AbstractIntegerPredefItem {

    private static final String plusName = "plus_int";

    public IntegerPlusPredef() {
        this(null, null, null, null, null);
    }

    /** creates an object which can build a Term plus(left, right)
     * @param nodeContent the content of the node, should be a "+"
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param left Term on the left side of the "+"-symbol
     * @param right Term on the right side of the "+"-symbol
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerPlusPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm left, AlgebraTerm right) {
        super(nodeContent, typeContext, program, Arrays.asList(left, right));
    }


    /** returns the plus symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return plus symbol from the program
     */
    public static DefFunctionSymbol getPlusSymbol(TypeContext typeContext, Program program) {
        IntegerPlusPredef ipp = new IntegerPlusPredef(null, typeContext, program, null, null);
        return ipp.getPlusSymbol();
    }


    /** returns the plus symbol
     * if necessary adds rules for plus to program and the types to typeContext if they do not exist yet
     * @return plus symbol from the program
     */
    public DefFunctionSymbol getPlusSymbol() {
        DefFunctionSymbol plusSym = this.program.getDefFunctionSymbol(IntegerPlusPredef.plusName);
        if (plusSym == null) {
            plusSym = this.createPlusRules();
        }
        return plusSym;
    }



    /** returns a Term representing the String
     */
    @Override
    public AlgebraTerm toTerm() {
        if (this.nodeContent.equals("+")) {
            return this.toPlusTerm();
        }
        return null;
    }



    /* creates a term with a plus symbol as root and with the two arguments which were passed as left and right
     */
    private AlgebraTerm toPlusTerm() {
        DefFunctionSymbol plusSym = this.getPlusSymbol();
        return AlgebraFunctionApplication.create(plusSym, this.getArguments());
    }



    /* creates the rules for plus
     */
    private DefFunctionSymbol createPlusRules() {
        DefFunctionSymbol plusSym = this.createAndAddDefFunSym(IntegerPlusPredef.plusName, 2);

        // setting commutativity of plus
        plusSym.setJCommutativity(0,true);
        plusSym.setJCommutativity(1,true);

        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));
        AlgebraTerm zeroTerm = AlgebraFunctionApplication.create(this.getZero());
        AlgebraTerm sx = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(xVar));
        AlgebraTerm sy = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(yVar));
        AlgebraTerm px = AlgebraFunctionApplication.create(this.getPred(), Arrays.asList(xVar));
        AlgebraTerm py = AlgebraFunctionApplication.create(this.getPred(), Arrays.asList(yVar));

        List<AlgebraTerm> plusArgs;

        // plus(0, 0) -> 0
        plusArgs = Arrays.asList(zeroTerm, zeroTerm);
        this.program.addRule(plusSym, Rule.create(AlgebraFunctionApplication.create(plusSym, plusArgs), zeroTerm));

        // plus(0, s(y)) -> s(y)
        plusArgs = Arrays.asList(zeroTerm, sy);
        this.program.addRule(plusSym, Rule.create(AlgebraFunctionApplication.create(plusSym, plusArgs), sy));

        // plus(0, p(y)) -> p(y)
        plusArgs = Arrays.asList(zeroTerm, py);
        this.program.addRule(plusSym, Rule.create(AlgebraFunctionApplication.create(plusSym, plusArgs), py));

        // plus(s(x), 0) -> s(x)
        plusArgs = Arrays.asList(sx, zeroTerm);
        this.program.addRule(plusSym, Rule.create(AlgebraFunctionApplication.create(plusSym, plusArgs), sx));

        // plus(p(x), 0) -> p(x)
        plusArgs = Arrays.asList(px, zeroTerm);
        this.program.addRule(plusSym, Rule.create(AlgebraFunctionApplication.create(plusSym, plusArgs), px));

        // create rules:
        //     plus(s(x),s(y)) -> s(s(plus(x,y)))
        //     plus(s(x),p(y)) -> plus(x,y)
        //     plus(p(x),s(y)) -> plus(x,y)
        //     plus(p(x),p(y)) -> p(p(plus(x,y)))
        List<SyntacticFunctionSymbol> sp = Arrays.asList((SyntacticFunctionSymbol)this.getSucc(), this.getPred());
        for(SyntacticFunctionSymbol sp1 : sp) {
            for (SyntacticFunctionSymbol sp2 : sp) {
                this.program.addRule(plusSym, this.createPlusRecRule(plusSym, sp1, sp2));
            }
        }

        return plusSym;
    }



    /* Helper for createPlusRules()
     * creates recursive rules of the form plus(sp1(x),sp2(y)) -> sp1^2(plus(x,y)) | plus(x,y)
     * if sp1==sp2 then the sp1^2 is added, otherwise they cancel each other
     */
    private Rule createPlusRecRule(DefFunctionSymbol plusSym, SyntacticFunctionSymbol sp1, SyntacticFunctionSymbol sp2) {
        List<AlgebraTerm> plusLArgs = new Vector<AlgebraTerm>();
        List<AlgebraTerm> plusRArgs = new Vector<AlgebraTerm>();
        AlgebraTerm right;

        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));

        plusLArgs.add(AlgebraFunctionApplication.create(sp1, Arrays.asList(xVar)));
        plusLArgs.add(AlgebraFunctionApplication.create(sp2, Arrays.asList(yVar)));

        plusRArgs = Arrays.asList(xVar, yVar);
        right = AlgebraFunctionApplication.create(plusSym, plusRArgs);
        if (sp1.equals(sp2)) {
            right = AlgebraFunctionApplication.create(sp1, Arrays.asList(right));
            right = AlgebraFunctionApplication.create(sp1, Arrays.asList(right));
        }

        return Rule.create(AlgebraFunctionApplication.create(plusSym, plusLArgs), right);
    }

}
