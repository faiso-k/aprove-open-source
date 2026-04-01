package aprove.verification.idpframework.Core.PredefinedFunctions;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class PredefinedSemanticsFactory {

    protected static Map<Func, Map<ImmutableList<? extends Domain>, PredefinedFunction<?, ?>>> functions =
        new HashMap<Func, Map<ImmutableList<? extends Domain>, PredefinedFunction<?, ?>>>();

    static final PfBoolean BOOLEAN_TRUE = PfBoolean.TRUE;

    static final PfBoolean BOOLEAN_FALSE = PfBoolean.FALSE;

    static final IFunctionSymbol<?> BOOLEAN_FS_TRUE = PfBoolean.FS_TRUE;

    static final IFunctionSymbol<?> BOOLEAN_FS_FALSE = PfBoolean.FS_FALSE;

    static final IFunctionApplication<?> BOOLEAN_TERM_TRUE = PfBoolean.TERM_TRUE;

    static final IFunctionApplication<?> BOOLEAN_TERM_FALSE = PfBoolean.TERM_FALSE;

    static ImmutableList<BooleanDomain> checkAllBooleanDomains(final ImmutableList<? extends Domain> domains) {
        if (!domains.isEmpty()) {
            final ArrayList<BooleanDomain> res =
                new ArrayList<BooleanDomain>(domains.size());
            for (final Domain dom : domains) {
                if (DomainFactory.BOOLEANS.equals(dom)) {
                    res.add((BooleanDomain) dom);
                } else {
                    return null;
                }
            }
            return ImmutableCreator.create(res);
        } else {
            return ImmutableCreator.create(Collections.<BooleanDomain> emptyList());
        }
    }

    static ImmutableList<? extends IntegerDomain<?>> checkAllIntDomains(final ImmutableList<? extends Domain> domains,
        final boolean checkEquality) {

        if (!domains.isEmpty()) {
            final ArrayList<IntegerDomain<?>> res =
                new ArrayList<IntegerDomain<?>>(domains.size());

            final Domain domain = domains.get(0);

            if (domain instanceof IntegerDomain) {
                for (final Domain dom : domains) {
                    if (!checkEquality || domain.equals(dom)) {
                        res.add((IntegerDomain<?>) dom);
                    } else {
                        return null;
                    }
                }
                return ImmutableCreator.create(res);
            } else {
                return null;
            }
        } else {
            return ImmutableCreator.create(Collections.<IntegerDomain<?>> emptyList());
        }
    }

    static ImmutableList<? extends IntegerDomain<?>> checkSameIntDomains(final ImmutableList<? extends Domain> domains) {
        return PredefinedSemanticsFactory.checkAllIntDomains(domains, true);
    }

    static PfBoolean createBoolean(final boolean value) {
        if (value) {
            return PfBoolean.TRUE;
        } else {
            return PfBoolean.FALSE;
        }
    }

    public static PredefinedFunction<?, ?> createFunction(final Func func,
        final ImmutableList<? extends SemiRingDomain<?>> domains) {
        synchronized (PredefinedSemanticsFactory.functions) {
            if (domains.size() != func.getArity()) {
                throw new IllegalArgumentException(
                    "arity does not match domain list");
            }
            Map<ImmutableList<? extends Domain>, PredefinedFunction<?, ?>> map =
                PredefinedSemanticsFactory.functions.get(func);
            if (map != null) {
                if (map.containsKey(domains)) {
                    return map.get(domains);
                }
            } else {
                map =
                    new HashMap<ImmutableList<? extends Domain>, PredefinedFunction<?, ?>>();
                PredefinedSemanticsFactory.functions.put(func, map);
            }

            // really create function
            final PredefinedFunction<?, ?> res =
                PredefinedSemanticsFactory.createFunction2(func, domains);
            map.put(domains, res);
            return res;
        }
    }

    @SuppressWarnings({ "unchecked", "rawtypes" })
    private static PredefinedFunction<?, ?> createFunction2(final Func func,
        final ImmutableList<? extends SemiRingDomain<?>> domains) {
        switch (func) {
        case Add: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfAdd(sameIntegerDomains);
            }
            break;
        }
        case Sub: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfSub(sameIntegerDomains);
            }
            break;
        }
        case Mul: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfMul(sameIntegerDomains);
            }
            break;
        }
        case Div: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfDiv(sameIntegerDomains);
            }
            break;
        }
        case Mod: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfMod(sameIntegerDomains);
            }
            break;
        }
        case UnaryMinus: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfUnaryMinus(sameIntegerDomains);
            }
            break;
        }
        case Cast: {
            throw new UnsupportedOperationException("cast not allowed");
        }
        case Eq: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfEq(sameIntegerDomains);
            }
            break;
        }
        case Neq: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfNeq(sameIntegerDomains);
            }
            break;
        }
        case Ge: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfGe(sameIntegerDomains);
            }
            break;
        }
        case Gt: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfGt(sameIntegerDomains);
            }
            break;
        }
        case Le: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfLe(sameIntegerDomains);
            }
            break;
        }
        case Lt: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfLt(sameIntegerDomains);
            }
            break;
        }
        case Bwand: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfBwand(sameIntegerDomains);
            }
            break;
        }
        case Bwor: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfBwor(sameIntegerDomains);
            }
            break;
        }
        case Bwxor: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfBwxor(sameIntegerDomains);
            }
            break;
        }
        case Bwnot: {
            final ImmutableList<? extends IntegerDomain<?>> sameIntegerDomains =
                PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return new PfBwnot(sameIntegerDomains);
            }
            break;
        }
        case Lor: {
            final ImmutableList<BooleanDomain> booleanDomains =
                PredefinedSemanticsFactory.checkAllBooleanDomains(domains);
            if (booleanDomains != null) {
                return new PfLor(booleanDomains);
            }
            break;
        }
        case Land: {
            final ImmutableList<BooleanDomain> booleanDomains =
                PredefinedSemanticsFactory.checkAllBooleanDomains(domains);
            if (booleanDomains != null) {
                return new PfLand(booleanDomains);
            }
            break;
        }
        case Lnot: {
            final ImmutableList<BooleanDomain> booleanDomains =
                PredefinedSemanticsFactory.checkAllBooleanDomains(domains);
            if (booleanDomains != null) {
                return new PfLnot(booleanDomains);
            }
            break;
        }
        }
        return null;
    }

    static <R extends IntRing<R>> PfInt<R> createInt(final R value,
        final IntegerDomain<R> domain) {

        if (domain.inRange(value)) {
            return new PfInt<R>(domain, value);
        } else {
            return null;
        }
    }

    static PfInt<BigInt> createInt(final String name, final IntegerDomain<BigInt> domain) {
        final BigInt value = PredefinedUtil.getIntValue(name, domain);
        if (value != null) {
            return new PfInt<BigInt>(domain, value);
        } else {
            return null;
        }
    }

    static <R extends IntRing<R>> IFunctionSymbol<R> createIntSym(final R value,
        final IntegerDomain<R> domain) {
        final PfInt<R> pfInt = PredefinedSemanticsFactory.createInt(value, domain);
        if (pfInt != null) {
            return pfInt.getSym();
        } else {
            return null;
        }
    }

    public static Collection<PredefinedFunction<?, ?>> getAllFunctions(final Collection<? extends Domain> domains) {
        final ArrayList<PredefinedFunction<?, ?>> res =
            new ArrayList<PredefinedFunction<?, ?>>();
        final Collection<IntegerDomain<?>> intDomains =
            new LinkedHashSet<IntegerDomain<?>>();
        for (final Domain domain : domains) {
            if (domain.isIntegerDomain()) {
                final IntegerDomain<?> intDomain = (IntegerDomain<?>) domain;
                intDomains.add(intDomain);
                for (final Func func : Func.values()) {
                    if (func.isIntFunction() && func != Func.Cast) {
                        final ArrayList<IntegerDomain<?>> doms =
                            new ArrayList<IntegerDomain<?>>(func.getArity());
                        for (int i = func.getArity() - 1; i >= 0; i--) {
                            doms.add(intDomain);
                        }
                        final ImmutableList<? extends IntegerDomain<?>> d =
                            ImmutableCreator.create(doms);
                        final PredefinedFunction<?, ?> preFunc =
                            PredefinedSemanticsFactory.createFunction(func, d);
                        res.add(preFunc);
                    }
                }
            } else if (domain.isBooleanDomain()) {
                final BooleanDomain boolDomain = (BooleanDomain) domain;
                for (final Func func : Func.values()) {
                    if (func.isBooleanFunction()) {
                        final ArrayList<BooleanDomain> doms =
                            new ArrayList<BooleanDomain>(func.getArity());
                        for (int i = func.getArity() - 1; i >= 0; i--) {
                            doms.add(boolDomain);
                        }
                        final ImmutableList<? extends BooleanDomain> d =
                            ImmutableCreator.create(doms);
                        final PredefinedFunction<?, ?> preFunc =
                            PredefinedSemanticsFactory.createFunction(func, d);
                        res.add(preFunc);
                    }
                }
            }
        }
        for (final IntegerDomain<?> fromDomain : intDomains) {
            for (final IntegerDomain<?> toDomain : intDomains) {
                if (!fromDomain.equals(toDomain)) {
                    final ArrayList<IntegerDomain<?>> castDomains =
                        new ArrayList<IntegerDomain<?>>();
                    castDomains.add(fromDomain);
                    castDomains.add(toDomain);
                    final ImmutableList<? extends SemiRingDomain<?>> d =
                        ImmutableCreator.create(castDomains);
                    final PredefinedFunction<?, ?> cast =
                        PredefinedSemanticsFactory.createFunction(Func.Cast, d);
                    res.add(cast);
                }
            }
        }
        return res;
    }

    @SuppressWarnings({ "unchecked", "rawtypes" })
    static <R extends SemiRing<R>> PredefinedConstructor<R> getConstructor(final SemiRingDomain<R> domain,
        final String name,
        final int arity) {
        if (arity == 0) {
            if (domain.getRing().isSameRing(BigInt.ZERO) && domain instanceof IntegerDomain) {
                final IntegerDomain castedDomain = (IntegerDomain) domain;
                final PfInt<BigInt> intConstr = PredefinedSemanticsFactory.createInt(name, castedDomain);
                return (PredefinedConstructor) intConstr;
            } else if (DomainFactory.BOOLEANS.equals(domain)) {
                if (PfBoolean.NAME_TRUE.equals(name)) {
                    return (PredefinedConstructor) PredefinedSemanticsFactory.BOOLEAN_TRUE;
                } else if (PfBoolean.NAME_FALSE.equals(name)) {
                    return (PredefinedConstructor) PredefinedSemanticsFactory.BOOLEAN_FALSE;
                }
            }
        }
        return null;
    }

    static <R extends IntRing<R>> IFunctionApplication<R> getIntTerm(final R value,
        final IntegerDomain<R> domain) {

        final PfInt<R> pfInt = PredefinedSemanticsFactory.createInt(value, domain);
        if (pfInt != null) {
            return pfInt.getTerm();
        } else {
            return null;
        }
    }

}
