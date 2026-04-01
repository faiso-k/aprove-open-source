package aprove.verification.oldframework.SMT.Solver.Z3;

import java.util.*;

import com.microsoft.z3.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.Sort;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class BuildExprVisitor implements ExpressionVisitor<Expr> {

    private final boolean autodeclare;
    private final Z3IntSolver solver;

    public BuildExprVisitor(Z3IntSolver solver, boolean autodeclare) {
        this.solver = solver;
        this.autodeclare = autodeclare;
    }

    @Override
    public <RV extends Sort, A0 extends Sort> Expr visit(Call1<RV, A0> call1) {
        Symbol1<RV, A0> sym = call1.getSym();
        Symbol1.Predef sem = sym.getSemantic();
        Expr a0 = call1.getA0().accept(this);
        Context c = this.solver.ctx;
        try {
            if (sem != null) {
                switch (sem) {
                case IntsAbs:
                    ArithExpr n = c.mkUnaryMinus((ArithExpr) a0);
                    return c.mkITE(c.mkGe((ArithExpr) a0, n), a0, n);
                case IntsNegate:
                    return c.mkUnaryMinus((ArithExpr) a0);
                case Not:
                    return c.mkNot((BoolExpr) a0);
                default:
                    throw new RuntimeException("Unhandled semantic: " + sem);
                }
            } else {
                FuncDecl f = this.solver.getFuncDecl(sym, this.autodeclare);
                return c.mkApp(f, a0);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort> Expr visit(Call2<RV, A0, A1> call2) {
        Symbol2<RV, A0, A1> sym = call2.getSym();
        Symbol2.Predef sem = sym.getSemantic();
        Expr a0 = call2.getA0().accept(this);
        Expr a1 = call2.getA1().accept(this);
        Context c = this.solver.ctx;
        try {
            if (sem != null) {
                switch (sem) {
                case IntsMod:
                    return c.mkMod((IntExpr) a0, (IntExpr) a1);
                default:
                    throw new RuntimeException("Unhandled semantic: " + sem);
                }
            } else {
                FuncDecl f = this.solver.getFuncDecl(sym, this.autodeclare);
                return c.mkApp(f, a0, a1);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> Expr visit(Call3<RV, A0, A1, A2> call3)
    {
        Symbol3<? extends Sort, A0, A1, A2> sym = call3.getSym();
        Symbol3.Predef sem = sym.getSemantic();
        Expr a0 = call3.getA0().accept(this);
        Expr a1 = call3.getA1().accept(this);
        Expr a2 = call3.getA2().accept(this);
        Context c = this.solver.ctx;
        try {
            if (sem != null) {
                switch (sem) {
                case ITE:
                    return c.mkITE((BoolExpr) a0, a1, a2);
                default:
                    throw new RuntimeException("Unhandled semantic: " + sem);
                }
            } else {
                FuncDecl f = this.solver.getFuncDecl(sym, this.autodeclare);
                return c.mkApp(f, a0, a1, a2);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public <A0 extends Sort> Expr visit(ChainableCall<A0> chainableCall) {
        ChainableSymbol<A0> sym = chainableCall.getSym();
        ChainableSymbol.Predef sem = sym.getSemantic();
        ImmutableList<SMTExpression<A0>> args = chainableCall.getArgs();
        final int l = args.size();
        Expr[] exps = new Expr[l];
        for (int i = 0; i < l; ++i) {
            exps[i] = args.get(i).accept(this);
        }
        assert l >= 2;
        Context c = this.solver.ctx;
        try {
            if (sem != null) {
                BoolExpr[] eqs = new BoolExpr[l - 1];
                switch (sem) {
                case Equivalent:
                    for (int i = 0; i < l - 1; ++i) {
                        eqs[i] = c.mkEq(exps[i], exps[i + 1]);
                    }
                    break;
                case IntsGreater:
                    for (int i = 0; i < l - 1; ++i) {
                        eqs[i] = c.mkGt((ArithExpr) exps[i], (ArithExpr) exps[i + 1]);
                    }
                    break;
                case IntsGreaterEqual:
                    for (int i = 0; i < l - 1; ++i) {
                        eqs[i] = c.mkGe((ArithExpr) exps[i], (ArithExpr) exps[i + 1]);
                    }
                    break;
                case IntsLess:
                    for (int i = 0; i < l - 1; ++i) {
                        eqs[i] = c.mkLt((ArithExpr) exps[i], (ArithExpr) exps[i + 1]);
                    }
                    break;
                case IntsLessEqual:
                    for (int i = 0; i < l - 1; ++i) {
                        eqs[i] = c.mkLe((ArithExpr) exps[i], (ArithExpr) exps[i + 1]);
                    }
                    break;
                default:
                    throw new RuntimeException("Unhandled semantic: " + sem);
                }
                if (eqs.length == 1) {
                    return eqs[0];
                }
                return c.mkAnd(eqs);
            } else {
                FuncDecl f = this.solver.getFuncDecl(sym, this.autodeclare);
                return c.mkApp(f, exps);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public <S extends Sort> Expr visit(Exists<S> exists) {
        Expr[] vars = this.visit(exists.getVars());
        Expr body = exists.getBody().accept(this);
        try {
            return this.solver.ctx.mkExists(vars, body, 1, null, null, null, null);
        } catch (final Z3Exception e) {
            throw new RuntimeException();
        }
    }

    @Override
    public <S extends Sort> Expr visit(Forall<S> forall) {
        Expr[] vars = this.visit(forall.getVars());
        Expr body = forall.getBody().accept(this);
        try {
            return this.solver.ctx.mkForall(vars, body, 1, null, null, null, null);
        } catch (final Z3Exception e) {
            throw new RuntimeException();
        }
    }

    private Expr[] visit(List<? extends Symbol0<? extends Sort>> l) {
        Expr[] vars = new Expr[l.size()];
        Iterator<? extends Symbol0<? extends Sort>> it = l.iterator();
        for (int i = 0; i < l.size(); i++) {
            Symbol0<? extends Sort> var = it.next();
            vars[i] = var.accept(this);
        }
        return vars;
    }

    @Override
    public Expr visit(IntConstant intConstant) {
        try {
            return this.solver.ctx.mkInt(intConstant.getConstant().toString());
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> Expr visit(LeftAssocCall<A0, A1> leftAssocCall) {
        LeftAssocSymbol<A0, A1> sym = leftAssocCall.getSym();
        LeftAssocSymbol.Predef sem = sym.getSemantic();
        ImmutableList<SMTExpression<A1>> args = leftAssocCall.getArgs();
        final int l = args.size();
        Expr[] exps = new Expr[l + 1];
        exps[0] = leftAssocCall.getFirst().accept(this);
        for (int i = 0; i < l; ++i) {
            exps[i + 1] = args.get(i).accept(this);
        }
        Context c = this.solver.ctx;
        try {
            if (sem != null) {
                switch (sem) {
                case And:
                    return c.mkAnd(Arrays.copyOf(exps, exps.length, BoolExpr[].class));
                case IntsAdd:
                    return c.mkAdd(Arrays.copyOf(exps, exps.length, ArithExpr[].class));
                case IntsDiv:
                    ArithExpr t = (ArithExpr) exps[0];
                    for (int i = 1; i < l + 1; ++i) {
                        t = c.mkDiv(t, (ArithExpr) exps[i]);
                    }
                    return t;
                case IntsSubtract:
                    return c.mkSub(Arrays.copyOf(exps, exps.length, ArithExpr[].class));
                case IntsTimes:
                    return c.mkMul(Arrays.copyOf(exps, exps.length, ArithExpr[].class));
                case Or:
                    return c.mkOr(Arrays.copyOf(exps, exps.length, BoolExpr[].class));
                case Xor:
                    BoolExpr x = (BoolExpr) exps[0];
                    for (int i = 1; i < l + 1; ++i) {
                        x = c.mkXor(x, (BoolExpr) exps[i]);
                    }
                    return x;
                default:
                    throw new RuntimeException("Unhandled semantic: " + sem);
                }
            } else {
                FuncDecl f = this.solver.getFuncDecl(sym, this.autodeclare);
                return c.mkApp(f, exps);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public <S extends Sort> Expr visit(Let<S> let) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public <A0 extends Sort> Expr visit(PairwiseCall<A0> pairwiseCall) {
        PairwiseSymbol<A0> sym = pairwiseCall.getSym();
        PairwiseSymbol.Predef sem = sym.getSemantic();
        ImmutableList<SMTExpression<A0>> args = pairwiseCall.getArgs();
        final int l = args.size();
        Expr[] exps = new Expr[l];
        for (int i = 0; i < l; ++i) {
            exps[i] = args.get(i).accept(this);
        }
        Context c = this.solver.ctx;
        try {
            if (sem != null) {
                switch (sem) {
                case Distinct:
                    return c.mkDistinct(exps);
                default:
                    throw new RuntimeException("Unhandled semantic: " + sem);
                }
            } else {
                FuncDecl f = this.solver.getFuncDecl(sym, this.autodeclare);
                return c.mkApp(f, exps);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> Expr visit(RightAssocCall<A0, A1> rightAssocCall) {
        RightAssocSymbol<A0, A1> sym = rightAssocCall.getSym();
        RightAssocSymbol.Predef sem = sym.getSemantic();
        ImmutableList<SMTExpression<A0>> args = rightAssocCall.getArgs();
        final int l = args.size();
        Expr[] exps = new Expr[l + 1];
        for (int i = 0; i < l; ++i) {
            exps[i] = args.get(i).accept(this);
        }
        exps[l] = rightAssocCall.getLast().accept(this);
        Context c = this.solver.ctx;
        try {
            if (sem != null) {
                switch (sem) {
                case Implies:
                    BoolExpr b = (BoolExpr) exps[l];
                    for (int i = l - 1; i >= 0; --i) {
                        b = c.mkImplies((BoolExpr) exps[i], b);
                    }
                    return b;
                default:
                    throw new RuntimeException("Unhandled semantic: " + sem);
                }
            } else {
                FuncDecl f = this.solver.getFuncDecl(sym, this.autodeclare);
                return c.mkApp(f, exps);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public <S extends Sort> Expr visit(Symbol0<S> symbol0) {
        if (symbol0.getSemantic() == null) {
            return this.solver.getVariable(symbol0, this.autodeclare);
        } else {
            try {
                switch (symbol0.getSemantic()) {
                    case False:
                        return this.solver.ctx.mkFalse();
                    case True:
                        return this.solver.ctx.mkTrue();
                    default:
                        throw new RuntimeException();
                }
            } catch (Z3Exception e) {
                throw new RuntimeException(e);
            }
        }
    }

}
