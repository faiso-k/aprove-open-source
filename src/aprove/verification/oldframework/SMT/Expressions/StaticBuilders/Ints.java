package aprove.verification.oldframework.SMT.Expressions.StaticBuilders;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class Ints {

    /** abs from theory Ints */
    public static SMTExpression<SInt> abs(SMTExpression<SInt> a) {
        return new Call1<>(Symbol1.IntsAbs, a);
    }

    /** + from theory Ints */
    @SafeVarargs
    public static SMTExpression<SInt> add(SMTExpression<SInt>... args) {
        return Ints.add(Arrays.asList(args));
    }

    /** + from theory Ints */
    public static SMTExpression<SInt> add(List<SMTExpression<SInt>> args) {
        if (args.size() == 0) {
            return Ints.constant(0);
        }
        if (args.size() == 1) {
            return args.get(0);
        }
        return new LeftAssocCall<>(LeftAssocSymbol.IntsAdd, args.get(0), Core.buildList(1, args.size() - 1, args));
    }

    /** int constant */
    public static SMTExpression<SInt> constant(BigInteger i) {
        return new IntConstant(i);
    }

    /** int constant */
    public static SMTExpression<SInt> constant(long i) {
        return new IntConstant(BigInteger.valueOf(i));
    }

    /** div from theory Ints */
    @SafeVarargs
    public static SMTExpression<SInt> div(SMTExpression<SInt>... args) {
        return Ints.div(Arrays.asList(args));
    }

    /** div from theory Ints */
    public static SMTExpression<SInt> div(List<SMTExpression<SInt>> args) {
        assert args.size() >= 2;
        return new LeftAssocCall<>(LeftAssocSymbol.IntsDiv, args.get(0), Core.buildList(1, args.size() - 1, args));
    }

    /** mod from theory Ints */
    public static SMTExpression<SInt> mod(SMTExpression<SInt> a, SMTExpression<SInt> b) {
        return new Call2<SInt, SInt, SInt>(Symbol2.IntsMod, a, b);
    }

    /** > from theory Ints */
    @SafeVarargs
    public static SMTExpression<SBool> greater(SMTExpression<SInt>... args) {
        return Ints.greater(Arrays.asList(args));
    }

    /** > from theory Ints */
    public static SMTExpression<SBool> greater(List<SMTExpression<SInt>> args) {
        assert args.size() >= 2;
        return new ChainableCall<>(ChainableSymbol.IntsGreater, Core.buildList(0, args.size() - 1, args));
    }

    /** >= from theory Ints */
    @SafeVarargs
    public static SMTExpression<SBool> greaterEqual(SMTExpression<SInt>... args) {
        return Ints.greaterEqual(Arrays.asList(args));
    }

    /** >= from theory Ints */
    public static SMTExpression<SBool> greaterEqual(List<SMTExpression<SInt>> args) {
        assert args.size() >= 2;
        return new ChainableCall<>(ChainableSymbol.IntsGreaterEqual, Core.buildList(0, args.size() - 1, args));
    }

    /** int variable */
    public static Symbol0<SInt> intVar() {
        return new Symbol0<>(SInt.representative);
    }

    /** named int variable */
    public static NamedSymbol0<SInt> intVar(final String n) {
        return new NamedSymbol0<>(SInt.representative, n);
    }

    /** < from theory Ints */
    @SafeVarargs
    public static SMTExpression<SBool> less(SMTExpression<SInt>... args) {
        return Ints.less(Arrays.asList(args));
    }

    /** < from theory Ints */
    public static SMTExpression<SBool> less(List<SMTExpression<SInt>> args) {
        assert args.size() >= 2;
        return new ChainableCall<>(ChainableSymbol.IntsLess, Core.buildList(0, args.size() - 1, args));
    }

    /** <= from theory Ints */
    @SafeVarargs
    public static SMTExpression<SBool> lessEqual(SMTExpression<SInt>... args) {
        return Ints.lessEqual(Arrays.asList(args));
    }

    /** <= from theory Ints */
    public static SMTExpression<SBool> lessEqual(List<SMTExpression<SInt>> args) {
        assert args.size() >= 2;
        return new ChainableCall<>(ChainableSymbol.IntsLessEqual, Core.buildList(0, args.size() - 1, args));
    }

    /** - (negation) from theory Ints */
    public static SMTExpression<SInt> negate(SMTExpression<SInt> a) {
        return new Call1<>(Symbol1.IntsNegate, a);
    }

    /** - (subtraction) from theory Ints */
    @SafeVarargs
    public static SMTExpression<SInt> subtract(SMTExpression<SInt>... args) {
        return Ints.subtract(Arrays.asList(args));
    }

    public static SMTExpression<SInt> subtract(List<SMTExpression<SInt>> args) {
        assert args.size() >= 2;
        return new LeftAssocCall<>(LeftAssocSymbol.IntsSubtract, args.get(0), Core.buildList(1, args.size() - 1, args));
    }

    /** * from theory Ints */
    @SafeVarargs
    public static SMTExpression<SInt> times(SMTExpression<SInt>... args) {
        return Ints.times(Arrays.asList(args));
    }

    /** * from theory Ints */
    public static SMTExpression<SInt> times(List<SMTExpression<SInt>> args) {
        if (args.size() == 0) {
            return Ints.constant(1);
        }
        if (args.size() == 1) {
            return args.get(0);
        }
        return new LeftAssocCall<>(LeftAssocSymbol.IntsTimes, args.get(0), Core.buildList(1, args.size() - 1, args));
    }
}
