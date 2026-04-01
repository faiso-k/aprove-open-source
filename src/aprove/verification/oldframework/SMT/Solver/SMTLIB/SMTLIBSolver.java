package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;
import immutables.*;

public class SMTLIBSolver implements SMTSolver {

    protected static final SExpList CheckSat = new SExpList(new SExpSymbol("check-sat"));

    protected static final SExp PopOne = new SExpList(new SExpSymbol("pop"), new SExpNumeral(BigInteger.valueOf(1)));

    protected static final SExp PushOne = new SExpList(new SExpSymbol("push"), new SExpNumeral(BigInteger.valueOf(1)));

    private static SExp getSortSExp(final Sort sort) {
        if (sort instanceof SBool) {
            return SMTLIBSymbols.Bool;
        }
        if (sort instanceof SInt) {
            return SMTLIBSymbols.Int;
        }
        throw new RuntimeException("Unhandled sort: " + sort);
    }

    protected final SMTLIBLogic logic;

    protected SExpProcessCommunicator proc;

    protected final ArrayDeque<LinkedHashMap<Symbol<?>, SExpSymbol>> state = new ArrayDeque<>();

    private ArrayList<SMTExpression<SBool>> all_assertions = new ArrayList<>();

    private final boolean enable_unsat_core;

    private int symbolCounter = 0;

    public SMTLIBSolver(final SMTLIBLogic logic, final SExpProcessCommunicator proc, boolean enable_unsat_core) {
        this.logic = logic;
        this.proc = proc;
        this.enable_unsat_core = enable_unsat_core;
        this.state.add(new LinkedHashMap<Symbol<?>, SExpSymbol>());

        proc.setExpectSuccess(false);
        try {
            proc.successCommand(new SExpList(
                                             SMTLIBSymbols.SetOption,
                                             SExpKeyword.get(":print-success"),
                                             SMTLIBSymbols.False));
            proc.successCommand(new SExpList(
                                             SMTLIBSymbols.SetOption,
                                             SExpKeyword.get(":produce-models"),
                                             SMTLIBSymbols.True));
            if (enable_unsat_core) {
                proc.successCommand(new SExpList(
                                                 SMTLIBSymbols.SetOption,
                                                 SExpKeyword.get(":produce-unsat-cores"),
                                                 SMTLIBSymbols.True));
            }
            proc.successCommand(new SExpList(SMTLIBSymbols.SetLogic, new SExpSymbol(this.logic.name())));
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }

    }

    @Override
    public void addAssertion(final SMTExpression<SBool> formula) {
        final BuildSExpVisitor v = new BuildSExpVisitor(this, true);
        try {
            SExpList exp;
            if (this.enable_unsat_core) {
                exp =
                      new SExpList(SMTLIBSymbols.Assert, new SExpList(
                                                                      new SExpSymbol("!"),
                                                                      formula.accept(v),
                                                                      SExpKeyword.get(":named"),
                                                                      new SExpSymbol("a" + this.all_assertions.size())));
                this.all_assertions.add(formula);
            } else {
                exp = new SExpList(SMTLIBSymbols.Assert, formula.accept(v));
            }
            this.proc.successCommand(exp);
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public YNM checkSAT() {
        try {
            final SExp status = this.proc.command(SMTLIBSolver.CheckSat);
            if (SMTLIBSymbols.Sat.equals(status)) {
                return YNM.YES;
            }
            if (SMTLIBSymbols.Unsat.equals(status)) {
                return YNM.NO;
            }
            if (SMTLIBSymbols.Unknown.equals(status)) {
                return YNM.MAYBE;
            }
            throw new RuntimeException("Unsupported result to check-sat command: " + status);
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void declare(final Symbol<?> sym) {
        this.getDeclaredAtom(sym, true);
    }

    @Override
    public void dispose() throws IOException {
        this.proc.dispose();
        this.proc = null;
    }

    @Override
    public ArrayList<SMTExpression<SBool>> getUnsatCore() {
        if (!this.enable_unsat_core) {
            throw new RuntimeException("unsat core not enabled");
        }
        try {
            ArrayList<SMTExpression<SBool>> answer = new ArrayList<>();
            SExpList l = (SExpList) this.proc.command(new SExpList(new SExpSymbol("get-unsat-core")));
            for (SExp assertion_name : l.getArgs()) {
                SExpSymbol n = (SExpSymbol) assertion_name;
                int num = Integer.parseInt(n.toString().substring(1));
                answer.add(this.all_assertions.get(num));
            }
            return answer;
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public Boolean getValue(final SBool sort, final SMTExpression<SBool> exp) {
        final BuildSExpVisitor v = new BuildSExpVisitor(this, false);
        try {
            final SExp result = this.proc.command(new SExpList(SMTLIBSymbols.GetValue, new SExpList(exp.accept(v))));
            final SExp r = result.get(0).get(1);
            if (SMTLIBSymbols.True.equals(r)) {
                return Boolean.TRUE;
            }
            if (SMTLIBSymbols.False.equals(r)) {
                return Boolean.FALSE;
            }
            throw new RuntimeException("Can't handle SMTLIB Bool expression: " + r);
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }

    }

    @Override
    public BigInteger getValue(final SInt sort, final SMTExpression<SInt> exp) {
        final BuildSExpVisitor v = new BuildSExpVisitor(this, false);
        try {
            final SExp result = this.proc.command(new SExpList(SMTLIBSymbols.GetValue, new SExpList(exp.accept(v))));
            final SExp r = result.get(0).get(1);
            return this.parseIntResult(r);
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ArrayList<Boolean> getValues(final SBool sort, final Iterable<SMTExpression<SBool>> exps) {
        final BuildSExpVisitor v = new BuildSExpVisitor(this, false);
        try {
            final ArrayList<SExp> sexpexps = new ArrayList<>();
            for (final SMTExpression<SBool> exp : exps) {
                sexpexps.add(exp.accept(v));
            }
            final SExp result =
                                this.proc
                                         .command(new SExpList(SMTLIBSymbols.GetValue,
                                                               new SExpList(ImmutableCreator.create(sexpexps))));
            final ArrayList<Boolean> bools = new ArrayList<>();
            if (!(result instanceof SExpList)) {
                throw new RuntimeException("expected list, got: " + result);
            }
            for (final SExp e : ((SExpList) result).getArgs()) {
                final SExp r = e.get(1);
                if (SMTLIBSymbols.True.equals(r)) {
                    bools.add(Boolean.TRUE);
                } else if (SMTLIBSymbols.False.equals(r)) {
                    bools.add(Boolean.FALSE);
                } else {
                    throw new RuntimeException("Can't handle SMTLIB Bool expression: " + r);
                }
            }
            return bools;
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public ArrayList<BigInteger> getValues(final SInt sort, final Iterable<SMTExpression<SInt>> exps) {
        final BuildSExpVisitor v = new BuildSExpVisitor(this, false);
        try {
            final ArrayList<SExp> sexpexps = new ArrayList<>();
            for (final SMTExpression<SInt> exp : exps) {
                sexpexps.add(exp.accept(v));
            }
            final SExp result =
                                this.proc
                                         .command(new SExpList(SMTLIBSymbols.GetValue,
                                                               new SExpList(ImmutableCreator.create(sexpexps))));
            final ArrayList<BigInteger> ints = new ArrayList<>();
            if (!(result instanceof SExpList)) {
                throw new RuntimeException("expected list, got: " + result);
            }
            for (final SExp e : ((SExpList) result).getArgs()) {
                ints.add(this.parseIntResult(e.get(1)));
            }
            return ints;
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void pop() {
        if (this.state.size() <= 1) {
            throw new RuntimeException("Tried to pop the last state.");
        }
        try {
            this.state.pop();
            this.proc.successCommand(SMTLIBSolver.PopOne);
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    @Override
    public void push() {
        try {
            final LinkedHashMap<Symbol<?>, SExpSymbol> newTop = new LinkedHashMap<>();
            newTop.putAll(this.state.getLast());
            this.state.push(newTop);
            this.proc.successCommand(SMTLIBSolver.PushOne);
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    protected Symbol<?> getSymbol(final SExpSymbol name) {
        // TODO introduce bidirectional map
        for (final Entry<Symbol<?>, SExpSymbol> e : this.state.getLast().entrySet()) {
            if (e.getValue().equals(name)) {
                return e.getKey();
            }
        }
        return null;
    }

    SExpSymbol getDeclaredAtom(final Symbol<?> sym, final boolean autodeclare) {
        final LinkedHashMap<Symbol<?>, SExpSymbol> top = this.state.getLast();
        SExpSymbol sexp = top.get(sym);
        if (sexp == null && autodeclare) {
            sexp = this.nameSymbol(sym);

            // build declare-fun/define-fun call
            if (sym instanceof Macro) {
                this.defineFun(sexp, (Macro) sym);
            } else {
                this.declareFun(sexp, sym);
            }
        }
        return sexp;
    }

    private void declareFun(final SExpSymbol name, final Symbol<?> sym) {
        final Sort[] args = sym.getArgumentSorts();
        final SExp[] vars = new SExp[args.length];
        for (int i = 0, l = args.length; i < l; ++i) {
            vars[i] = SMTLIBSolver.getSortSExp(args[i]);
        }
        final SExpList decl =
                              new SExpList(SMTLIBSymbols.declareFun,
                                           name,
                                           new SExpList(vars),
                                           SMTLIBSolver.getSortSExp(sym
                                                                       .getReturnSort()));
        try {
            this.proc.successCommand(decl);
        } catch (IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    private void defineFun(final SExpSymbol sexp, final Macro<?> m) {
        final BuildSExpVisitor v = new BuildSExpVisitor(this, true);
        final Sort[] args = m.getArgumentSorts();
        SExp sorted_vars;
        SMTExpression<?> bodySMT;
        SExp body;
        Symbol0 a0, a1, a2;

        switch (args.length) {
            case 1:
                final Macro1<?, ?> m1 = (Macro1<?, ?>) m;
                a0 = args[0].createVariable();
                sorted_vars = new SExpList(new SExpList(this.nameSymbol(a0), SMTLIBSolver.getSortSExp(args[0])));
                bodySMT = m1.body(a0);
                body = bodySMT.accept(v);
                break;
            case 2:
                final Macro2<?, ?, ?> m2 = (Macro2<?, ?, ?>) m;
                a0 = args[0].createVariable();
                a1 = args[1].createVariable();
                sorted_vars =
                              new SExpList(new SExpList(this.nameSymbol(a0), SMTLIBSolver.getSortSExp(args[0])),
                                           new SExpList(
                                                        this.nameSymbol(a1),
                                                        SMTLIBSolver.getSortSExp(args[1])));
                bodySMT = m2.body(a0, a1);
                body = bodySMT.accept(v);
                break;
            case 3:
                final Macro3<?, ?, ?, ?> m3 = (Macro3<?, ?, ?, ?>) m;
                a0 = args[0].createVariable();
                a1 = args[1].createVariable();
                a2 = args[2].createVariable();
                sorted_vars =
                              new SExpList(new SExpList(this.nameSymbol(a0), SMTLIBSolver.getSortSExp(args[0])),
                                           new SExpList(
                                                        this.nameSymbol(a1),
                                                        SMTLIBSolver.getSortSExp(args[1])),
                                           new SExpList(this.nameSymbol(a2), SMTLIBSolver.getSortSExp(args[2])));
                bodySMT = m3.body(a0, a1, a2);
                body = bodySMT.accept(v);
                break;
            default:
                throw new RuntimeException("unhandled macro arity: " + args.length);
        }
        try {
            final SExpList cmd =
                                 new SExpList(
                                              SMTLIBSymbols.defineFun,
                                              sexp,
                                              sorted_vars,
                                              SMTLIBSolver.getSortSExp(m.getReturnSort()),
                                              body);
            this.proc.successCommand(cmd);
        } catch (AbortionException | IOException | ParserException e) {
            throw new RuntimeException(e);
        }
    }

    private SExpSymbol nameSymbol(final Symbol<?> sym) {
        final LinkedHashMap<Symbol<?>, SExpSymbol> top = this.state.getLast();
        final SExpSymbol sexp = new SExpSymbol("s" + this.symbolCounter++);
        top.put(sym, sexp);
        return sexp;
    }

    private BigInteger parseIntResult(final SExp r) {
        if (r instanceof SExpNumeral) {
            final SExpNumeral n = (SExpNumeral) r;
            return n.getBigInteger();
        }
        throw new RuntimeException("Can't handle SMTLIB Int expression: " + r);
    }

}
