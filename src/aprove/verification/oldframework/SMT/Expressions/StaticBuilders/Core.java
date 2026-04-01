package aprove.verification.oldframework.SMT.Expressions.StaticBuilders;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class Core {

    /** false from theory Core */
    public static final SMTExpression<SBool> False = Symbol0.False;

    /** true from theory Core */
    public static final SMTExpression<SBool> True = Symbol0.True;

    /** and from theory Core */
    @SafeVarargs
    public static SMTExpression<SBool> and(SMTExpression<SBool>... args) {
        return Core.and(Arrays.asList(args));
    }

    /** and from theory Core */
    public static SMTExpression<SBool> and(List<SMTExpression<SBool>> args) {
        if (args.size() == 0) {
            return Core.True;
        }
        if (args.size() == 1) {
            return args.get(0);
        }
        return new LeftAssocCall<>(LeftAssocSymbol.And, args.get(0), Core.buildList(1, args.size() - 1, args));
    }

    public static SMTExpression<SBool> boolVar() {
        return new Symbol0<>(SBool.representative);
    }

    public static SMTExpression<SBool> boolVar(String n) {
        return new NamedSymbol0<>(SBool.representative, n);
    }

    static <T extends Sort> ImmutableList<SMTExpression<T>> buildList(int start, int end, List<SMTExpression<T>> args) {
        int l = args.size();
        assert start >= 0 && start < l;
        assert end >= 0 && end < l;
        assert start <= end;
        ArrayList<SMTExpression<T>> rv = new ArrayList<>();
        for (int i = start; i < end + 1; ++i) {
            assert args.get(i) != null;
            rv.add(args.get(i));
        }
        return ImmutableCreator.create(rv);
    }

    public static <S extends Sort, A0 extends Sort> SMTExpression<S> call(Symbol1<S, A0> sym, SMTExpression<A0> a0) {
        return new Call1<>(sym, a0);
    }

    public static <S extends Sort, A0 extends Sort, A1 extends Sort> SMTExpression<S> call(
        Symbol2<S, A0, A1> sym,
        SMTExpression<A0> a0,
        SMTExpression<A1> a1)
    {
        return new Call2<>(sym, a0, a1);
    }

    public static <S extends Sort, A0 extends Sort, A1 extends Sort, A2 extends Sort> SMTExpression<S> call(
        Symbol3<S, A0, A1, A2> sym,
        SMTExpression<A0> a0,
        SMTExpression<A1> a1,
        SMTExpression<A2> a2)
    {
        return new Call3<>(sym, a0, a1, a2);
    }

    /** distinct from theory Core */
    @SafeVarargs
    public static <T extends Sort> SMTExpression<SBool> distinct(SMTExpression<T>... args) {
        return Core.distinct(Arrays.asList(args));
    }

    /** distinct from theory Core */
    public static <T extends Sort> SMTExpression<SBool> distinct(List<SMTExpression<T>> args) {
        assert args.size() >= 2;
        // at this point, we hack in the polymorphism of distinct by using an unsafe cast
        @SuppressWarnings("unchecked")
        PairwiseSymbol<T> sym = (PairwiseSymbol<T>) PairwiseSymbol.Distinct;
        return new PairwiseCall<>(sym, Core.buildList(0, args.size() - 1, args));
    }

    /** = from theory Core */
    @SafeVarargs
    public static <T extends Sort> SMTExpression<SBool> equivalent(SMTExpression<T>... args) {
        return Core.equivalent(Arrays.asList(args));
    }

    /** = from theory Core */
    public static <T extends Sort> SMTExpression<SBool> equivalent(List<SMTExpression<T>> args) {
        assert args.size() >= 2;
        // at this point, we hack in the polymorphism of '=' by using an unchecked cast
        @SuppressWarnings("unchecked")
        ChainableSymbol<T> sym = (ChainableSymbol<T>) ChainableSymbol.Equivalent;
        return new ChainableCall<>(sym, Core.buildList(0, args.size() - 1, args));
    }

    /** => from theory Core */
    @SafeVarargs
    public static SMTExpression<SBool> implies(SMTExpression<SBool>... args) {
        return Core.implies(Arrays.asList(args));
    }

    /** => from theory Core */
    public static SMTExpression<SBool> implies(List<SMTExpression<SBool>> args) {
        assert args.size() >= 2;
        return new RightAssocCall<>(RightAssocSymbol.Implies, Core.buildList(0, args.size() - 2, args), args.get(args
            .size() - 1));
    }

    /** ite (if-then-else) from theory Core */
    public static <T extends Sort> SMTExpression<T> ite(
        SMTExpression<SBool> cond,
        SMTExpression<T> thenCase,
        SMTExpression<T> elseCase)
    {
        @SuppressWarnings("unchecked")
        SMTExpression<T> call =
            (SMTExpression<T>) new Call3<>(
                Symbol3.ITE,
                SBool.representative,
                cond,
                (SMTExpression<Sort>) thenCase,
                (SMTExpression<Sort>) elseCase);
        return call;
    }

    /** not from theory Core */
    public static SMTExpression<SBool> not(SMTExpression<SBool> a) {
        return Core.call(Symbol1.Not, a);
    }

    /** or from theory Core */
    @SafeVarargs
    public static SMTExpression<SBool> or(SMTExpression<SBool>... args) {
        return Core.or(Arrays.asList(args));
    }

    /** or from theory Core */
    public static SMTExpression<SBool> or(List<SMTExpression<SBool>> args) {
        if (args.size() == 0) {
            return Core.False;
        }
        if (args.size() == 1) {
            return args.get(0);
        }
        return new LeftAssocCall<>(LeftAssocSymbol.Or, args.get(0), Core.buildList(1, args.size() - 1, args));
    }

    /** xor from theory Core */
    public static SMTExpression<SBool> xor(@SuppressWarnings("unchecked") SMTExpression<SBool>... args) {
        return Core.xor(Arrays.asList(args));
    }

    /** xor from theory Core */
    public static SMTExpression<SBool> xor(List<SMTExpression<SBool>> args) {
        assert args.size() >= 2;
        return new LeftAssocCall<>(LeftAssocSymbol.Xor, args.get(0), Core.buildList(1, args.size() - 1, args));
    }

    /** exists (from core term definition, not theory Core) */
    public static <S extends Sort> SMTExpression<S> exists(S s, List<? extends Symbol0<? extends Sort>> vars, SMTExpression<S> body) {
        return new Exists<S>(s, ImmutableCreator.create(vars), body);
    }

    /** forall (from core term definition, not theory Core) */
    public static <S extends Sort> SMTExpression<S> forall(S s, List<? extends Symbol0<? extends Sort>> vars, SMTExpression<S> body) {
        return new Forall<S>(s, ImmutableCreator.create(vars), body);
    }
}
