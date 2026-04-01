package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

public class IntegerQuotPredef extends AbstractIntegerPredefItem {

    private static final String quotName = "quot_int";
    private static final String quotCeilName = "quotCeil_int";
    private static final String minusSName = "minusS_int";

    public IntegerQuotPredef() {
        this(null,null,null,null,null);
    }

    /** creates an object which can build a Term quot(left, right)
     * @param nodeContent the content of the node, should be a "/"
     * @param typeContext the current TypeContext in which types of newly created functions should be inserted into
     * @param program the current Program in which newly created rules should be inserted into
     * @param left Term on the left side of the "/"-symbol
     * @param right Term on the right side of the "/"-symbol
     * @return object which builds requested term upon call of toTerm()
     */
    public IntegerQuotPredef(String nodeContent, TypeContext typeContext, Program program, AlgebraTerm left, AlgebraTerm right) {
        super(nodeContent, typeContext, program, Arrays.asList(left, right));
    }


    /** returns the quot symbol
     * if necessary adds rules for quot to program and the types to typeContext if they do not exist yet
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return quot symbol from the program
     */
    public static DefFunctionSymbol getQuotSymbol(TypeContext typeContext, Program program) {
        IntegerQuotPredef iqp = new IntegerQuotPredef(null, typeContext, program, null, null);
        return iqp.getQuotSymbol();
    }

    /** returns the quot symbol
     * if necessary adds rules for quot to program and the types to typeContext if they do not exist yet
     * @return quot symbol from the program
     */
    public DefFunctionSymbol getQuotSymbol() {
        DefFunctionSymbol quotSym = this.program.getDefFunctionSymbol(IntegerQuotPredef.quotName);
        if (quotSym == null) {
            quotSym = this.createQuotRules();
        }
        return quotSym;
    }


    /** returns the minusS symbol (where minusS(x,y) = max{0, x-y} for x,y >= 0)
     * if necessary the rules are created and added to the program
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return minusS symbol from the program
     */
    public static DefFunctionSymbol getMinusSSymbol(TypeContext typeContext, Program program) {
        IntegerQuotPredef iqp = new IntegerQuotPredef(null, typeContext, program, null, null);
        return iqp.getMinusSSymbol();
    }

    /** returns the minusS symbol (where minusS(x,y) = max{0, x-y})
     * if necessary the rules are created and added to the program
     * @return minusS symbol from the program
     */
    public DefFunctionSymbol getMinusSSymbol() {
        DefFunctionSymbol minusSSym = this.program.getDefFunctionSymbol(IntegerQuotPredef.minusSName);
        if (minusSSym == null) {
            minusSSym = this.createMinusSRules();
        }
        return minusSSym;
    }


    /** returns the quotCeil symbol (where quotCeil(x,y) = ceil(x/y) for x,y >= 0)
     * if necessary the rules are created and added to the program
     * @param typeContext the typeContext to insert new types into
     * @param program the program to insert new rules into
     * @return quotCeil symbol from the program
     */
    public static DefFunctionSymbol getQuotCeilSymbol(TypeContext typeContext, Program program) {
        IntegerQuotPredef iqp = new IntegerQuotPredef(null, typeContext, program, null, null);
        return iqp.getQuotCeilSymbol();
    }

    /** returns the quotCeil symbol (where quotCeil(x,y) = ceil(x/y) for x >= 0, y > 0)
     * if necessary the rules are created and added to the program
     * @return quotCeil symbol from the program
     */
    private DefFunctionSymbol getQuotCeilSymbol() {
        DefFunctionSymbol quotCeilSym = this.program.getDefFunctionSymbol(IntegerQuotPredef.quotCeilName);
        if (quotCeilSym == null) {
            quotCeilSym = this.createQuotCeilRules();
        }
        return quotCeilSym;
    }


    @Override
    public AlgebraTerm toTerm() {
        DefFunctionSymbol quotSym = this.getQuotSymbol();
        return AlgebraFunctionApplication.create(quotSym, this.arguments);
    }



    /* creates the rules for the quot symbol
     * these rules convert everything into positive integers and prepare for rounding downwards
     * (the ceil rules always return the smallest integer bigger or equal than the result)
     */
    private DefFunctionSymbol createQuotRules() {
        DefFunctionSymbol quotSym = this.createAndAddDefFunSym(IntegerQuotPredef.quotName, 2);
        DefFunctionSymbol quotCeilSym = this.getQuotCeilSymbol();


        List<SyntacticFunctionSymbol> SPList = Arrays.asList((SyntacticFunctionSymbol)this.getSucc(), this.getPred());

        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));
        AlgebraTerm zeroTerm = AlgebraFunctionApplication.create(this.getZero());
        List<AlgebraTerm> quotArgs;

        // creates rules
        //    quot(0,s(y)) -> 0
        //    quot(0,p(y)) -> 0
        for(SyntacticFunctionSymbol sp : SPList) {
            quotArgs = new Vector<AlgebraTerm>();
            quotArgs.add(zeroTerm);
            quotArgs.add(AlgebraFunctionApplication.create(sp, Arrays.asList(yVar)));
            this.program.addRule(quotSym, Rule.create(AlgebraFunctionApplication.create(quotSym, quotArgs), zeroTerm));
        }

        // create rules
        //    quot(s(x),s(y)) -> quotCeil(minusS(s(x),y),s(y))
        //    quot(s(x),p(y)) -> neg(quotCeil(minusS(s(x),neg(y)),neg(p(y))))
        //    quot(p(x),s(y)) -> neg(quotCeil(minusS(neg(s(x)),y),s(y)))
        //    quot(p(x),p(y)) -> quotCeil(minusS(neg(p(x)),neg(y)),neg(p(y)))
        for(SyntacticFunctionSymbol sp1 : SPList) {
            for(SyntacticFunctionSymbol sp2 : SPList) {
                this.program.addRule(quotSym, this.createQuot2QuotCeilRule(quotSym, quotCeilSym,  sp1, sp2));
            }
        }

        return quotSym;
    }


    /* helper for createQuotRules()
     * creates a rule quot(sp1(x),sp2(y)) -> [neg]quotCeil(minusS([neg]sp1(x), [neg]y), [neg]sp2(y))
     * where negation on arguments is introduced if the term is negative (i.e. starts with a pred)
     * and negation of the whole rhs is introduced if sp1 != sp2
     */
    private Rule createQuot2QuotCeilRule(DefFunctionSymbol quotSym, DefFunctionSymbol quotCeilSym, SyntacticFunctionSymbol sp1, SyntacticFunctionSymbol sp2) {
        DefFunctionSymbol minusSSym = this.getMinusSSymbol();
        DefFunctionSymbol negSym = IntegerNegPredef.getNegSymbol(this.typeContext, this.program);


        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));
        List<AlgebraTerm> quotArgs = new Vector<AlgebraTerm>();
        List<AlgebraTerm> minusSArgs = new Vector<AlgebraTerm>();

        quotArgs.add(AlgebraFunctionApplication.create(sp1, Arrays.asList(xVar)));
        quotArgs.add(AlgebraFunctionApplication.create(sp2, Arrays.asList(yVar)));

        boolean negateRHS = false;
        // check the arguments
        AlgebraTerm arg = AlgebraFunctionApplication.create(sp1, Arrays.asList(xVar));
        if(sp1.equals(this.getPred())) {
            arg = AlgebraFunctionApplication.create(negSym, Arrays.asList(arg));
            negateRHS ^= true;
        }
        minusSArgs.add(arg);

        arg = yVar;
        AlgebraTerm quotCeilArg2 = AlgebraFunctionApplication.create(sp2, Arrays.asList(yVar));
        if(sp2.equals(this.getPred())) {
            arg = AlgebraFunctionApplication.create(negSym, Arrays.asList(arg));
            quotCeilArg2 = AlgebraFunctionApplication.create(negSym, Arrays.asList(quotCeilArg2));
            negateRHS ^= true;
        }
        minusSArgs.add(arg);


        AlgebraTerm minusSTerm = AlgebraFunctionApplication.create(minusSSym, minusSArgs);
        AlgebraTerm right = AlgebraFunctionApplication.create(quotCeilSym, Arrays.asList(minusSTerm, quotCeilArg2));
        if(negateRHS) {
            right = AlgebraFunctionApplication.create(negSym, Arrays.asList(right));
        }

        return Rule.create(AlgebraFunctionApplication.create(quotSym, quotArgs), right);
    }



    /* helper for createQuotRules()
     * creates the FunctionSymbol quotCeil and adds the correspoding rules
     * uses minusS
     * returns the FunctionSymbol quotS
     */
    private DefFunctionSymbol createQuotCeilRules() {
        DefFunctionSymbol quotCeilSym = this.createAndAddDefFunSym(IntegerQuotPredef.quotCeilName, 2);


        List<AlgebraTerm> quotCeilArgs;
        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));
        AlgebraTerm zeroTerm = AlgebraFunctionApplication.create(this.getZero());

        // create rule quotCeil(0, s(y)) -> 0
        quotCeilArgs = new Vector<AlgebraTerm>();
        quotCeilArgs.add(zeroTerm);
        quotCeilArgs.add(AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(yVar)));
        this.program.addRule(quotCeilSym, Rule.create(AlgebraFunctionApplication.create(quotCeilSym, quotCeilArgs), zeroTerm));


        DefFunctionSymbol minusSSym = this.getMinusSSymbol();

        // create rule quotCeil(s(x),s(y)) -> s(quotCeil(minusS(x,y),s(y)))
        quotCeilArgs = new Vector<AlgebraTerm>();
        quotCeilArgs.add(AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(xVar)));
        quotCeilArgs.add(AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(yVar)));
        AlgebraTerm left = AlgebraFunctionApplication.create(quotCeilSym, quotCeilArgs);
        List<AlgebraTerm> minusSArgs = Arrays.asList(xVar, yVar);
        quotCeilArgs = new Vector<AlgebraTerm>();
        quotCeilArgs.add(AlgebraFunctionApplication.create(minusSSym, minusSArgs));
        quotCeilArgs.add(AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(yVar)));
        AlgebraTerm right = AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(AlgebraFunctionApplication.create(quotCeilSym, quotCeilArgs)));
        this.program.addRule(quotCeilSym, Rule.create(left, right));

        return quotCeilSym;
    }


    /* creates the FunctionSymbol minusS and returns it
     * where minusS(x,y) = max {0, x-y} for x,y >= 0
     */
    private DefFunctionSymbol createMinusSRules() {
        DefFunctionSymbol minusSSym = this.createAndAddDefFunSym(IntegerQuotPredef.minusSName, 2);


        AlgebraTerm xVar = AlgebraVariable.create(VariableSymbol.create("x"));
        AlgebraTerm yVar = AlgebraVariable.create(VariableSymbol.create("y"));
        AlgebraTerm zeroTerm = AlgebraFunctionApplication.create(this.getZero());

        // create the rule minusS(0,y) -> 0
        List<AlgebraTerm> minusSArgs = new Vector<AlgebraTerm>();
        minusSArgs.add(zeroTerm);
        minusSArgs.add(yVar);
        this.createMinusSRule(minusSSym, minusSArgs, zeroTerm);

        // creates the rule minusS(x,0) -> x
        minusSArgs = new Vector<AlgebraTerm>();
        minusSArgs.add(xVar);
        minusSArgs.add(zeroTerm);
        this.createMinusSRule(minusSSym, minusSArgs, xVar);

        // creates the rule minusS(s(x),s(y)) -> minusS(x,y)
        minusSArgs = new Vector<AlgebraTerm>();
        minusSArgs.add(AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(xVar)));
        minusSArgs.add(AlgebraFunctionApplication.create(this.getSucc(), Arrays.asList(yVar)));
        this.createMinusSRule(minusSSym, minusSArgs, AlgebraFunctionApplication.create(minusSSym, Arrays.asList(xVar, yVar)));


        return minusSSym;
    }

    /* helper for createMinusSRules()
     * creates a rule minusSSym(lMinusSArgs) -> right and adds it to the program
     */
    private void createMinusSRule(DefFunctionSymbol minusSSym, List<AlgebraTerm> lMinusSArgs, AlgebraTerm right) {
        this.program.addRule(minusSSym, Rule.create(AlgebraFunctionApplication.create(minusSSym, lMinusSArgs), right));
    }

}
