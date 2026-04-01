package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol0.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;
import immutables.*;

class BuildSExpVisitor implements ExpressionVisitor<SExp> {
    private final boolean autodeclare;
    private final SMTLIBSolver solver;

    BuildSExpVisitor(final SMTLIBSolver solver, final boolean autodeclare) {
        this.solver = solver;
        this.autodeclare = autodeclare;
    }

    public SExp getDeclaredAtom(final Symbol<?> sym) {
        final SExp rv = this.solver.getDeclaredAtom(sym, this.autodeclare);
        if (rv == null) {
            throw new RuntimeException("Undeclared symbol " + sym.toString());
        }
        return rv;
    }

    private SExp getSemanticSymbol(final ChainableSymbol.Predef sem) {
        switch (sem) {
        case Equivalent:
            return SMTLIBSymbols.Equivalent;
        case IntsGreater:
            return SMTLIBSymbols.IntsGreater;
        case IntsGreaterEqual:
            return SMTLIBSymbols.IntsGreaterEqual;
        case IntsLess:
            return SMTLIBSymbols.IntsLess;
        case IntsLessEqual:
            return SMTLIBSymbols.IntsLessEqual;
        default:
            throw new RuntimeException("unhandled semantic: " + sem);
        }
    }

    private SExp getSemanticSymbol(final LeftAssocSymbol.Predef sem) {
        switch (sem) {
        case And:
            return SMTLIBSymbols.And;
        case IntsAdd:
            return SMTLIBSymbols.IntsAdd;
        case IntsDiv:
            return SMTLIBSymbols.IntsDiv;
        case IntsSubtract:
            return SMTLIBSymbols.IntsSubtract;
        case IntsTimes:
            return SMTLIBSymbols.IntsTimes;
        case Or:
            return SMTLIBSymbols.Or;
        case Xor:
            return SMTLIBSymbols.Xor;
        default:
            throw new RuntimeException("unhandled semantic: " + sem);
        }
    }

    private SExp getSemanticSymbol(final PairwiseSymbol.Predef sem) {
        switch (sem) {
        case Distinct:
            return SMTLIBSymbols.Distinct;
        default:
            throw new RuntimeException("unhandled semantic: " + sem);
        }
    }

    private SExp getSemanticSymbol(final Predef sem) {
        switch (sem) {
        case True:
            return SMTLIBSymbols.True;
        case False:
            return SMTLIBSymbols.False;
        default:
            throw new RuntimeException("unhandled semantic: " + sem);
        }
    }

    private SExp getSemanticSymbol(final RightAssocSymbol.Predef sem) {
        switch (sem) {
        case Implies:
            return SMTLIBSymbols.Implies;
        default:
            throw new RuntimeException("unhandled semantic: " + sem);
        }
    }

    private SExp getSemanticSymbol(final Symbol1.Predef sem) {
        switch (sem) {
        case IntsAbs:
            return SMTLIBSymbols.IntsAbs;
        case IntsNegate:
            return SMTLIBSymbols.IntsNegate;
        case Not:
            return SMTLIBSymbols.Not;
        default:
            throw new RuntimeException("unhandled semantic: " + sem);
        }
    }

    private SExp getSemanticSymbol(final Symbol2.Predef sem) {
        switch (sem) {
        case IntsMod:
            return SMTLIBSymbols.IntsMod;
        default:
            throw new RuntimeException("unhandled semantic: " + sem);
        }
    }

    private SExp getSemanticSymbol(final Symbol3.Predef sem) {
        switch (sem) {
        case ITE:
            return SMTLIBSymbols.ITE;
        default:
            throw new RuntimeException("unhandled semantic: " + sem);
        }
    }

    @Override
    public <RV extends Sort, A0 extends Sort> SExp visit(final Call1<RV, A0> call1) {
        final Symbol1<RV, A0> sym = call1.getSym();
        final Symbol1.Predef sem = sym.getSemantic();
        SExp f;
        if (sem != null) {
            f = this.getSemanticSymbol(sem);
        } else {
            f = this.getDeclaredAtom(sym);
        }
        final SExp a0 = call1.getA0().accept(this);
        return new SExpList(f, a0);
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort> SExp visit(final Call2<RV, A0, A1> call2) {
        final Symbol2<RV, A0, A1> sym = call2.getSym();
        final Symbol2.Predef sem = sym.getSemantic();
        SExp f;
        if (sem != null) {
            f = this.getSemanticSymbol(sem);
        } else {
            f = this.getDeclaredAtom(sym);
        }
        final SExp a0 = call2.getA0().accept(this);
        final SExp a1 = call2.getA1().accept(this);
        return new SExpList(f, a0, a1);
    }

    @Override
    public <RV extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> SExp visit(final Call3<RV, A0, A1, A2> call3)
    {
        final Symbol3<? extends Sort, A0, A1, A2> sym = call3.getSym();
        final Symbol3.Predef sem = sym.getSemantic();
        SExp f;
        if (sem != null) {
            f = this.getSemanticSymbol(sem);
        } else {
            f = this.getDeclaredAtom(sym);
        }
        final SExp a0 = call3.getA0().accept(this);
        final SExp a1 = call3.getA1().accept(this);
        final SExp a2 = call3.getA2().accept(this);
        return new SExpList(f, a0, a1, a2);
    }

    @Override
    public <A0 extends Sort> SExp visit(final ChainableCall<A0> chainableCall) {
        final ChainableSymbol<A0> sym = chainableCall.getSym();
        final ChainableSymbol.Predef sem = sym.getSemantic();
        SExp f;
        if (sem != null) {
            f = this.getSemanticSymbol(sem);
        } else {
            f = this.getDeclaredAtom(sym);
        }
        final ArrayList<SExp> call = new ArrayList<>();
        call.add(f);
        for (final SMTExpression<A0> c : chainableCall.getArgs()) {
            call.add(c.accept(this));
        }
        return new SExpList(ImmutableCreator.create(call));
    }

    @Override
    public <S extends Sort> SExp visit(final Exists<S> exists) {
        //final ArrayList<SExp> vars = new ArrayList<>();
        final SExp body = exists.getBody().accept(this);

        //        for (Symbol0<?> v : exists.getVars()) {
        //            vars.add(this.getDeclaredAtom(v));
        //        }

        final ArrayList<SExp> varDecls = new ArrayList<>();
        for (final Symbol0<?> v : exists.getVars()) {
            final ArrayList<SExp> decl = new ArrayList<>(2);

            decl.add(this.getDeclaredAtom(v));
            decl.add(new SExpSymbol(v.getType().toString()));
            varDecls.add(new SExpList(ImmutableCreator.create(decl)));
        }

        return new SExpList(SMTLIBSymbols.Exists, new SExpList(ImmutableCreator.create(varDecls)), body);

        // return new SExpList(SMTLIBSymbols.Exists, new SExpList(ImmutableCreator.create(vars)), body);
    }

    @Override
    public <S extends Sort> SExp visit(final Forall<S> forall) {
        final ArrayList<SExp> vars = new ArrayList<>();
        final SExp body = forall.getBody().accept(this);
        for (final Symbol0<?> v : forall.getVars()) {
            vars.add(this.getDeclaredAtom(v));
        }
        return new SExpList(SMTLIBSymbols.Forall, new SExpList(ImmutableCreator.create(vars)), body);
    }

    @Override
    public SExp visit(final IntConstant intConstant) {
        final BigInteger i = intConstant.getConstant();
        if (i.compareTo(BigInteger.ZERO) >= 0) {
            return new SExpNumeral(i);
        } else {
            return new SExpList(SMTLIBSymbols.IntsNegate, new SExpNumeral(i.negate()));
        }
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> SExp visit(final LeftAssocCall<A0, A1> leftAssocCall) {
        final LeftAssocSymbol<A0, A1> sym = leftAssocCall.getSym();
        final LeftAssocSymbol.Predef sem = sym.getSemantic();
        SExp f;
        if (sem != null) {
            f = this.getSemanticSymbol(sem);
        } else {
            f = this.getDeclaredAtom(sym);
        }
        final ArrayList<SExp> call = new ArrayList<>();
        call.add(f);
        call.add(leftAssocCall.getFirst().accept(this));
        for (final SMTExpression<A1> c : leftAssocCall.getArgs()) {
            call.add(c.accept(this));
        }
        return new SExpList(ImmutableCreator.create(call));
    }

    @Override
    public <S extends Sort> SExp visit(final Let<S> let) {
        final ArrayList<SExp> vars = new ArrayList<>();
        final SExp body = let.getBody().accept(this);
        for (final VarBinding<?> v : let.getBindings()) {
            vars.add(new SExpList(this.getDeclaredAtom(v.getVar()), v.getExpr().accept(this)));
        }
        return new SExpList(SMTLIBSymbols.Forall, new SExpList(ImmutableCreator.create(vars)), body);
    }

    @Override
    public <A0 extends Sort> SExp visit(final PairwiseCall<A0> pairwiseCall) {
        final PairwiseSymbol<A0> sym = pairwiseCall.getSym();
        final PairwiseSymbol.Predef sem = sym.getSemantic();
        SExp f;
        if (sem != null) {
            f = this.getSemanticSymbol(sem);
        } else {
            f = this.getDeclaredAtom(sym);
        }
        final ArrayList<SExp> call = new ArrayList<>();
        call.add(f);
        for (final SMTExpression<A0> c : pairwiseCall.getArgs()) {
            call.add(c.accept(this));
        }
        return new SExpList(ImmutableCreator.create(call));
    }

    @Override
    public <A0 extends Sort, A1 extends Sort> SExp visit(final RightAssocCall<A0, A1> rightAssocCall) {
        final RightAssocSymbol<A0, A1> sym = rightAssocCall.getSym();
        final RightAssocSymbol.Predef sem = sym.getSemantic();
        SExp f;
        if (sem != null) {
            f = this.getSemanticSymbol(sem);
        } else {
            f = this.getDeclaredAtom(sym);
        }
        final ArrayList<SExp> call = new ArrayList<>();
        call.add(f);
        for (final SMTExpression<A0> c : rightAssocCall.getArgs()) {
            call.add(c.accept(this));
        }
        call.add(rightAssocCall.getLast().accept(this));
        return new SExpList(ImmutableCreator.create(call));
    }

    @Override
    public <S extends Sort> SExp visit(final Symbol0<S> symbol0) {
        final Symbol0.Predef sem = symbol0.getSemantic();
        if (sem != null) {
            return this.getSemanticSymbol(sem);
        } else {
            return this.getDeclaredAtom(symbol0);
        }
    }
}
