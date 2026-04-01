package aprove.verification.oldframework.SMT.Solver.Z3;

import java.io.*;
import java.math.*;
import java.util.*;

import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.Sort;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.Model;

public class Z3IntSolver implements Z3Solver {

    /** Dummy object used for locking, forcing context creation to be sequential. */
    private static final Object contextCreationLockObject = new Object();

    final Context ctx;
    @SuppressWarnings("unused")
    private SMTLIBLogic logic;
    private Solver solver;

    ArrayDeque<LinkedHashMap<Symbol<?>, AST>> state = new ArrayDeque<>();

    private int symbolNumber = 0;
    private final Abortion abortion;

    /**
     * Currently, this solver does not work with child abortions. To make sure that a certain request to
     * the solver only consumes a certain amount of time, use the timeout argument, which specifies a
     * timeout in milliseconds.
     *
     * @param logic The used logic.
     * @param timeout The timeout in milliseconds.
     * @param abortion The aborter (Note that child aborter do not work properly, pass the parent aborter!).
     */
    public Z3IntSolver(SMTLIBLogic logic, int timeout, Abortion abortion) {
        this.abortion = abortion;
        this.logic = logic;
        this.state.push(new LinkedHashMap<Symbol<?>, AST>());
        try {
            synchronized (Z3IntSolver.contextCreationLockObject) {
                this.ctx = new Context();
            }
            this.solver = this.ctx.mkSolver();
            Params p = this.ctx.mkParams();
            p.add("timeout", timeout);
            this.solver.setParameters(p);
            abortion.addListenerOrFire(new AbortionListener() {

                @Override
                public void abortionFired(Abortion source, String reason) {
                    try {
                        Z3IntSolver.this.ctx.interrupt();
                    } catch (Z3Exception e) {
                        throw new RuntimeException(e);
                    }
                }
            });
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void addAssertion(SMTExpression<SBool> formula) {
        ExpressionVisitor<Expr> visitor = new BuildExprVisitor(this, true);
        BoolExpr expr = (BoolExpr) formula.accept(visitor);
        try {
            this.solver.add(expr);
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public YNM checkSAT() {
        this.abortion.checkAbortion();
        try {
            Status s = this.solver.check();
            switch (s) {
                case SATISFIABLE:
                    return YNM.YES;
                case UNKNOWN:
                    return YNM.MAYBE;
                case UNSATISFIABLE:
                    return YNM.NO;
                default:
                    throw new RuntimeException("unhandled status: " + s);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    private final com.microsoft.z3.Symbol createSymbol(Symbol<?> sym) throws Z3Exception {
        if (sym instanceof NamedSymbol) {
            return this.ctx.mkSymbol(((NamedSymbol<?>) sym).getName());
        } else {
            return this.ctx.mkSymbol(this.symbolNumber++);
        }
    }

    @Override
    public void declare(Symbol<?> sym) {
        LinkedHashMap<Symbol<?>, AST> top = this.state.getLast();
        if (top.containsKey(sym)) {
            throw new RuntimeException("symbol already declared");
        }
        if (sym instanceof Symbol0<?>) {
            top.put(sym, this.generateVariable((Symbol0<?>) sym));
        } else {
            top.put(sym, this.generateFunc(sym));
        }
    }

    private FuncDecl generateFunc(Symbol<?> sym) {
        try {
            com.microsoft.z3.Symbol name = this.createSymbol(sym);

            com.microsoft.z3.Sort range = this.getZ3Sort(sym.getReturnSort());
            Sort[] args = sym.getArgumentSorts();
            int l = args.length;
            com.microsoft.z3.Sort[] domain = new com.microsoft.z3.Sort[l];

            for (int i = 0; i < l; ++i) {
                domain[i] = this.getZ3Sort(args[i]);
            }
            return this.ctx.mkFuncDecl(name, domain, range);
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    Expr generateVariable(Symbol0<?> sym) {
        Sort sort = sym.getReturnSort();
        try {
            if (sort instanceof SBool) {
                return this.ctx.mkBoolConst(createSymbol(sym));
            }
            if (sort instanceof SInt) {
                return this.ctx.mkIntConst(createSymbol(sym));
            }
            throw new RuntimeException("unhandled sort: " + sort);
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    FuncDecl getFuncDecl(Symbol<?> sym, boolean autodeclare) {
        if (!this.state.getLast().containsKey(sym) && autodeclare) {
            this.declare(sym);
        }
        FuncDecl decl = (FuncDecl) this.state.getLast().get(sym);
        if (decl == null) {
            throw new RuntimeException("undeclared symbol: " + sym);
        }
        return decl;
    }

    @Override
    public Optional<Model> getModel() {
        try {
            return new Z3ModelToModel(this.solver.getModel(), this.state.getFirst()).transform();
        } catch (Z3Exception e) {
            return Optional.empty();
        }
    }

    @Override
    public Boolean getValue(SBool sort, SMTExpression<SBool> exp) {
        try {
            com.microsoft.z3.Model model = this.solver.getModel();
            ExpressionVisitor<Expr> visitor = new BuildExprVisitor(this, false);
            Expr expr = exp.accept(visitor);
            BoolExpr b = (BoolExpr) model.eval(expr, true);
            Z3_lbool z = b.getBoolValue();
            switch (z) {
                case Z3_L_FALSE:
                    return false;
                case Z3_L_TRUE:
                    return true;
                default:
                    throw new RuntimeException("unhandled value: " + z);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public BigInteger getValue(SInt sort, SMTExpression<SInt> exp) {
        try {
            com.microsoft.z3.Model model = this.solver.getModel();
            ExpressionVisitor<Expr> visitor = new BuildExprVisitor(this, false);
            Expr expr = exp.accept(visitor);
            IntNum i = (IntNum) model.eval(expr, true);
            return i.getBigInteger();
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ArrayList<Boolean> getValues(SBool sort, Iterable<SMTExpression<SBool>> exps) {
        try {
            com.microsoft.z3.Model model = this.solver.getModel();
            ExpressionVisitor<Expr> visitor = new BuildExprVisitor(this, false);
            ArrayList<Boolean> results = new ArrayList<>();
            for (SMTExpression<SBool> exp : exps) {
                BoolExpr r = (BoolExpr) model.eval(exp.accept(visitor), true);
                switch (r.getBoolValue()) {
                case Z3_L_FALSE:
                    results.add(Boolean.FALSE);
                    break;
                case Z3_L_TRUE:
                    results.add(Boolean.TRUE);
                    break;
                default:
                    throw new RuntimeException("unhandled value: " + r.getBoolValue());
                }
            }
            return results;
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ArrayList<BigInteger> getValues(SInt sort, Iterable<SMTExpression<SInt>> exps) {
        try {
            com.microsoft.z3.Model model = this.solver.getModel();
            ExpressionVisitor<Expr> visitor = new BuildExprVisitor(this, false);
            ArrayList<BigInteger> results = new ArrayList<>();
            for (SMTExpression<SInt> exp : exps) {
                IntNum r = (IntNum) model.eval(exp.accept(visitor), true);
                results.add(r.getBigInteger());
            }
            return results;
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    Expr getVariable(Symbol0<?> sym, boolean autodeclare) {
        if (!this.state.getLast().containsKey(sym) && autodeclare) {
            this.declare(sym);
        }
        Expr expr = (Expr) this.state.getLast().get(sym);
        if (expr == null) {
            throw new RuntimeException("undeclared symbol: " + sym);
        }
        return expr;
    }

    private com.microsoft.z3.Sort getZ3Sort(Sort sort) throws Z3Exception {
        if (sort instanceof SBool) {
            return this.ctx.getBoolSort();
        }
        if (sort instanceof SInt) {
            return this.ctx.getIntSort();
        }
        throw new RuntimeException("unsupported sort: " + sort);
    }

    @Override
    public void pop() {
        try {
            this.solver.pop();
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void push() {
        try {
            this.solver.push();
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void dispose() throws IOException {
        this.ctx.dispose();
    }

    @Override
    public void reset() {
        try {
            this.solver.reset();
            this.state.clear();
            this.state.push(new LinkedHashMap<Symbol<?>, AST>());
            this.symbolNumber = 0;
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ArrayList<SMTExpression<SBool>> getUnsatCore() {
        throw new RuntimeException("not implemented yet");
    }
}
