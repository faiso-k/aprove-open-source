package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerNegPredef extends AbstractIntegerPredefItem {

    private static final String negName = "neg_int";

    public IntegerNegPredef() {
        this(null, null, null, null);
    }

    /** creates an object which can build a Term neg(negTerm)
     * @param nodeContent the content of the node, can be a "-" or a "+"
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param negTerm Term following the symbol in nodeContent
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerNegPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm negTerm) {
        super(nodeContent, typeContext, program, Arrays.asList(negTerm));
    }


    /** returns the negation symbol
     * if necessary adds rules for neg to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return negation symbol from the program
     */
    public static DefFunctionSymbol getNegSymbol(TypeContext typeContext, Program program) {
        IntegerNegPredef inp = new IntegerNegPredef(null, typeContext, program, null);
        return inp.getNegSymbol();
    }


    /** returns the negation symbol
     * if necessary adds rules for neg to program and the types to typeContext if they do not exist yet
     * @return negation symbol from the program
     */
    public DefFunctionSymbol getNegSymbol() {
        DefFunctionSymbol negSym = this.program.getDefFunctionSymbol(IntegerNegPredef.negName);
        if (negSym == null) {
            negSym = this.createNegRules();
        }
        return negSym;
    }


    /** returns a negated term if the nodeContent this object was built with was "-",
     * returns the term itself in case it was a "+",
     * and returns null otherwise
     */
    @Override
    public AlgebraTerm toTerm() {
        if (this.nodeContent.equals("-")) {
            return this.toNegTerm();
        }
        else if (this.nodeContent.equals("+")) {
            return this.getNegTerm();
        }
        return null;
    }



    private AlgebraTerm getNegTerm() {
        return this.arguments.get(0);
    }


    // creation of terms per operation
    private AlgebraTerm toNegTerm() {

        // if negTerm is an Integer Term, negate in place and do not create rules
        if (this.isIntegerTerm(this.getNegTerm())) {
            return this.negateIntegerTerm(this.getNegTerm());
        }

        DefFunctionSymbol negSym = this.getNegSymbol();
        return AlgebraFunctionApplication.create(negSym, this.arguments);
    }


    /* negates a Term which only consists of zero, pred, or succ
     */
    private AlgebraTerm negateIntegerTerm(AlgebraTerm t) {
        AlgebraTerm result = t;
        Symbol sym = result.getSymbol();
        if (sym.equals(this.getSucc())) {
            List<AlgebraTerm> args = new Vector<AlgebraTerm>();
            args.add(this.negateIntegerTerm(result.getArgument(0)));
            return AlgebraFunctionApplication.create(this.getPred(), args);
        }
        else if (sym.equals(this.getPred())) {
            List<AlgebraTerm> args = new Vector<AlgebraTerm>();
            args.add(this.negateIntegerTerm(result.getArgument(0)));
            return AlgebraFunctionApplication.create(this.getSucc(), args);
        }
        else if (sym.equals(this.getZero())) {
            return result;
        } else {
            return null;
        }
    }



    /* creates rule neg(sp1(x)) -> sp2(neg(x)),
     * i.e. should be called with sp1/2=succ/pred or sp1/2=pred/succ
    */
    private Rule createNegRecRule(DefFunctionSymbol neg, SyntacticFunctionSymbol sp1, SyntacticFunctionSymbol sp2) {
        List<AlgebraTerm> negLArgs = new Vector<AlgebraTerm>();
        List<AlgebraTerm> negRArgs = new Vector<AlgebraTerm>();
        List<AlgebraTerm> sp1Args = new Vector<AlgebraTerm>();
        List<AlgebraTerm> sp2Args = new Vector<AlgebraTerm>();

        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));

        sp1Args.add(xVar);
        negLArgs.add(AlgebraFunctionApplication.create(sp1, sp1Args));

        negRArgs.add(xVar);
        sp2Args.add(AlgebraFunctionApplication.create(neg, negRArgs));

        return Rule.create(AlgebraFunctionApplication.create(neg, negLArgs), AlgebraFunctionApplication.create(sp2, sp2Args));
    }


    private DefFunctionSymbol createNegRules() {
        DefFunctionSymbol negSym = this.createAndAddDefFunSym(IntegerNegPredef.negName, 1);

        List<AlgebraTerm> negArgs = new Vector<AlgebraTerm>();

        // neg(0) -> 0
        AlgebraTerm zeroTerm = AlgebraFunctionApplication.create(this.getZero());
        negArgs.add(zeroTerm);
        this.program.addRule(negSym, Rule.create(AlgebraFunctionApplication.create(negSym, negArgs), zeroTerm));

        // create rules:
        //     neg(s(x)) -> p(neg(x))
        //     neg(p(x)) -> s(neg(x))
        this.program.addRule(negSym, this.createNegRecRule(negSym, this.getSucc(), this.getPred()));
        this.program.addRule(negSym, this.createNegRecRule(negSym, this.getPred(), this.getSucc()));

        return negSym;
    }

}
