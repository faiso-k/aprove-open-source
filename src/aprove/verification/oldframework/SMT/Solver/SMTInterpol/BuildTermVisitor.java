package aprove.verification.oldframework.SMT.Solver.SMTInterpol;

import java.math.*;

import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.Sort;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import de.uni_freiburg.informatik.ultimate.logic.*;
import immutables.*;

/**
 * Converts AProVE's internal SMTLIB2 representation to SMTInterpol's
 * internal SMTLIB2 representation, possibly declaring identifiers
 * in SMTInterpol in the process.
 *
 * Heavily inspired by BuildExprVisitor for Z3.
 *
 * @author fuhs
 */
public class BuildTermVisitor implements ExpressionVisitor<Term> {

    private final boolean autodeclare;
    private final SMTInterpolIntSolver solver;
    private final Script script;

    /** A whole bunch of predefined function names from SMTLIB2 theories
     *  (avoid inline string literals, mov 'em where you can see 'em together)
     */
    /* ints theory */
    private static final String UNARY_MINUS = "-";
    private static final String BINARY_MINUS = "-";
    private static final String PLUS = "+";
    private static final String TIMES = "*";
    private static final String DIV = "div";
    private static final String MOD = "mod";
    private static final String ABS = "abs";

    private static final String GE = ">=";
    private static final String GT = ">";
    private static final String LE = "<=";
    private static final String LT = "<";

    /* core theory */
    private static final String DISTINCT = "distinct";
    private static final String EQ = "=";
    private static final String IFF = BuildTermVisitor.EQ;
    private static final String AND = "and";
    private static final String OR = "or";
    private static final String NOT = "not";
    private static final String XOR = "xor";
    private static final String IMPLIES = "=>";
    private static final String ITE = "ite";

    private static final String TRUE = "true";
    private static final String FALSE = "false";

    public BuildTermVisitor(SMTInterpolIntSolver solver, boolean autodeclare) {
        this.solver = solver;
        this.script = solver.getScript();
        this.autodeclare = autodeclare;
    }

    @Override
    public <RV extends Sort, A0 extends Sort> Term visit(Call1<RV, A0> call1) {
        Symbol1<RV, A0> sym = call1.getSym();
        Symbol1.Predef sem = sym.getSemantic();
        Term a0 = call1.getA0().accept(this);
        final Term res;
        final String operator;
        if (sem != null) {
            switch (sem) {
            case IntsAbs: {
                operator = BuildTermVisitor.ABS;
                break;
            }
            case IntsNegate: {
                operator = BuildTermVisitor.UNARY_MINUS;
                break;
            }
            case Not: {
                operator = BuildTermVisitor.NOT;
                break;
            }
            default:
                throw new RuntimeException("Unhandled semantic: " + sem);
            }
        } else {
            operator = this.solver.getFuncDecl(sym, this.autodeclare);
        }
        res = this.script.term(operator, a0);
        return res;
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort> Term visit(Call2<RV, A0, A1> call2) {
        Symbol2<RV, A0, A1> sym = call2.getSym();
        Symbol2.Predef sem = sym.getSemantic();
        Term a0 = call2.getA0().accept(this);
        Term a1 = call2.getA1().accept(this);
        final Term res;
        final String operator;
        if (sem != null) {
            switch (sem) {
                case IntsMod: {
                    operator = BuildTermVisitor.MOD;
                    break;
                }
            default:
                throw new RuntimeException("Unhandled semantic: " + sem);
            }
        } else {
            operator = this.solver.getFuncDecl(sym, this.autodeclare);
        }
        res = this.script.term(operator, a0, a1);
        return res;
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> Term visit(Call3<RV, A0, A1, A2> call3)
    {
        Symbol3<? extends Sort, A0, A1, A2> sym = call3.getSym();
        Symbol3.Predef sem = sym.getSemantic();
        Term a0 = call3.getA0().accept(this);
        Term a1 = call3.getA1().accept(this);
        Term a2 = call3.getA2().accept(this);
        final Term res;
        final String operator;
        if (sem != null) {
            switch (sem) {
            case ITE: {
                operator = BuildTermVisitor.ITE;
                break;
            }
            default:
                throw new RuntimeException("Unhandled semantic: " + sem);
            }
        } else {
            operator = this.solver.getFuncDecl(sym, this.autodeclare);
        }
        res = this.script.term(operator, a0, a1, a2);
        return res;
    }

    @Override
    public <A0 extends Sort> Term visit(ChainableCall<A0> chainableCall) {
        ChainableSymbol<A0> sym = chainableCall.getSym();
        ChainableSymbol.Predef sem = sym.getSemantic();
        ImmutableList<SMTExpression<A0>> args = chainableCall.getArgs();
        final int l = args.size();
        Term[] exps = new Term[l];
        for (int i = 0; i < l; ++i) {
            exps[i] = args.get(i).accept(this);
        }
        assert l >= 2;
        final Term res;
        final String operator;
        if (sem != null) {
            Term[] eqs = new Term[l - 1];
            switch (sem) {
            case Equivalent: {
                operator = BuildTermVisitor.EQ;
                break;
            }
            case IntsGreater: {
                operator = BuildTermVisitor.GT;
                break;
            }
            case IntsGreaterEqual: {
                operator = BuildTermVisitor.GE;
                break;
            }
            case IntsLess: {
                operator = BuildTermVisitor.LT;
                break;
            }
            case IntsLessEqual: {
                operator = BuildTermVisitor.LE;
                break;
            }
            default:
                throw new RuntimeException("Unhandled semantic: " + sem);
            }
            for (int i = 0; i < l - 1; ++i) {
                eqs[i] = this.script.term(operator, exps[i], exps[i + 1]);
            }
            if (eqs.length == 1) {
                res = eqs[0];
            } else {
                res = this.script.term(BuildTermVisitor.AND, eqs);
            }
        } else {
            operator = this.solver.getFuncDecl(sym, this.autodeclare);
            res = this.script.term(operator, exps);
        }
        return res;
    }

    @Override
    public <S extends Sort> Term visit(Exists<S> exists) {
        throw new NotYetImplementedException("Existential quantification not handled yet.");
        //        for (Symbol0<?> v : exists.getVars()) {
        //
        //        }
        //        return this.solver.ctx.mkExists(arg0, arg1, arg2, arg3, arg4, arg5, arg6);
    }

    @Override
    public <S extends Sort> Term visit(Forall<S> forall) {
        throw new NotYetImplementedException("Universal quantification not handled yet.");
    }

    @Override
    public Term visit(IntConstant intConstant) {
        BigInteger value = intConstant.getConstant();
        Term res = this.script.numeral(value);
        return res;
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> Term visit(LeftAssocCall<A0, A1> leftAssocCall) {
        LeftAssocSymbol<A0, A1> sym = leftAssocCall.getSym();
        LeftAssocSymbol.Predef sem = sym.getSemantic();
        ImmutableList<SMTExpression<A1>> args = leftAssocCall.getArgs();
        final int l = args.size();
        Term[] exps = new Term[l + 1];
        exps[0] = leftAssocCall.getFirst().accept(this);
        for (int i = 0; i < l; ++i) {
            exps[i + 1] = args.get(i).accept(this);
        }
        final Term res;
        final String operator;
        if (sem != null) {
            switch (sem) {
            case And: {
                operator = BuildTermVisitor.AND;
                break;
            }
            case IntsAdd: {
                operator = BuildTermVisitor.PLUS;
                break;
            }
            case IntsDiv: {
                operator = BuildTermVisitor.DIV;
                break;
            }
            case IntsSubtract: {
                operator = BuildTermVisitor.BINARY_MINUS;
                break;
            }
            case IntsTimes: {
                operator = BuildTermVisitor.TIMES;
                break;
            }
            case Or: {
                operator = BuildTermVisitor.OR;
                break;
            }
            case Xor: {
                operator = BuildTermVisitor.XOR;
                break;
            }
            default:
                throw new RuntimeException("Unhandled semantic: " + sem);
            }
        } else {
            operator = this.solver.getFuncDecl(sym, this.autodeclare);
        }
        res = this.script.term(operator, exps);
        return res;
    }

    @Override
    public <S extends Sort> Term visit(Let<S> let) {
        // TODO Auto-generated method stub
        throw new NotYetImplementedException("Don't know (yet?) how to handle 'let'.");
    }

    @Override
    public <A0 extends Sort> Term visit(PairwiseCall<A0> pairwiseCall) {
        PairwiseSymbol<A0> sym = pairwiseCall.getSym();
        PairwiseSymbol.Predef sem = sym.getSemantic();
        ImmutableList<SMTExpression<A0>> args = pairwiseCall.getArgs();
        final int l = args.size();
        Term[] exps = new Term[l];
        for (int i = 0; i < l; ++i) {
            exps[i] = args.get(i).accept(this);
        }
        final Term res;
        final String operator;
        if (sem != null) {
            switch (sem) {
            case Distinct: {
                operator = BuildTermVisitor.DISTINCT;
                break;
            }
            default:
                throw new RuntimeException("Unhandled semantic: " + sem);
            }
        } else {
            operator = this.solver.getFuncDecl(sym, this.autodeclare);
        }
        res = this.script.term(operator, exps);
        return res;
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> Term visit(RightAssocCall<A0, A1> rightAssocCall) {
        RightAssocSymbol<A0, A1> sym = rightAssocCall.getSym();
        RightAssocSymbol.Predef sem = sym.getSemantic();
        ImmutableList<SMTExpression<A0>> args = rightAssocCall.getArgs();
        final int l = args.size();
        Term[] exps = new Term[l + 1];
        for (int i = 0; i < l; ++i) {
            exps[i] = args.get(i).accept(this);
        }
        exps[l] = rightAssocCall.getLast().accept(this);
        final Term res;
        final String operator;
        if (sem != null) {
            switch (sem) {
            case Implies: {
                /*
                    BoolExpr b = (BoolExpr) exps[l];
                    for (int i = l - 1; i >= 0; --i) {
                        b = c.mkImplies((BoolExpr) exps[i], b);
                    }
                    return b;
                    */
                operator = BuildTermVisitor.IMPLIES;
                break;
            }
            default:
                throw new RuntimeException("Unhandled semantic: " + sem);
            }
        } else {
            operator = this.solver.getFuncDecl(sym, this.autodeclare);
        }
        res = this.script.term(operator, exps);
        return res;
    }

    @Override
    public <S extends Sort> Term visit(Symbol0<S> symbol0) {
        // the next line also registers the name with the solver if needed
        String name = this.solver.getFuncDecl(symbol0, this.autodeclare);
        Term res = this.script.term(name);
        return res;
    }
}
