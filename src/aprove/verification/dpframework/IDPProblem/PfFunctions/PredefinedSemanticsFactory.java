package aprove.verification.dpframework.IDPProblem.PfFunctions;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv2.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class PredefinedSemanticsFactory {

    protected static Map<Func, Map<ImmutableList<? extends Domain>, PredefinedFunction<? extends Domain>>> functions = new LinkedHashMap<Func, Map<ImmutableList<? extends Domain>,PredefinedFunction<? extends Domain>>>();

    public static PredefinedConstructor getConstructor(Domain domain, TRSTerm t) {
        if (t.isVariable()) {
            return null;
        } else {
            return PredefinedSemanticsFactory.getConstructor(domain, ((TRSFunctionApplication)t).getRootSymbol());
        }
    }

    public static PredefinedConstructor getConstructor(Domain domain, FunctionSymbol fs) {
        if (domain instanceof IntegerDomain) {
            PfInt intConstr = PredefinedSemanticsFactory.getInt(fs, (IntegerDomain) domain);
            if (intConstr == null) {
                PfUndefinedInt undef = new PfUndefinedInt((IntegerDomain) domain);
                if (undef.getSym().equals(fs)) {
                    return undef;
                }
            }
            return intConstr;
        } else if (DomainFactory.BOOLEAN.equals(domain)) {
            return PredefinedSemanticsFactory.getBoolean(fs);
        } else {
            return null;
        }
    }

    public static BigInteger getIntValue(TRSTerm t, IntegerDomain domain) {
        if (!t.isVariable()) {
            FunctionSymbol fs = ((TRSFunctionApplication) t).getRootSymbol();
            return PredefinedSemanticsFactory.getIntValue(fs, domain);
        }
        return null;
    }

    public static BigInteger getIntValue(FunctionSymbol fs, IntegerDomain domain) {
        if (fs.getArity() > 0 || fs.getName().equals(InstanceTransformer.EOC)) {
            return null;
        }
        if (fs.getName().matches("-?\\d+")) {
            BigInteger value = new BigInteger(fs.getName());
            if (domain.inRange(value)) {
                return value;
            } else {
                return null;
            }
        } else {
            return null;
        }
    }

    public static PfUndefinedInt getUndefinedInt(IntegerDomain domain) {
        return new PfUndefinedInt(domain);
    }

    public static TRSFunctionApplication getIntTerm(BigIntImmutable value, IntegerDomain domain) {
        PfInt pfInt = PredefinedSemanticsFactory.getInt(value, domain);
        if (pfInt != null) {
            return pfInt.getTerm();
        } else {
            return null;
        }
    }

    public static FunctionSymbol getIntSym(BigIntImmutable value, IntegerDomain domain) {
        PfInt pfInt = PredefinedSemanticsFactory.getInt(value, domain);
        if (pfInt != null) {
            return pfInt.getSym();
        } else {
            return null;
        }
    }

    public static PfInt getInt(TRSTerm t, IntegerDomain domain) {
        BigInteger value = PredefinedSemanticsFactory.getIntValue(t, domain);
        if (value != null) {
            return new PfInt(domain, BigIntImmutable.create(value));
        } else {
            return null;
        }
    }

    public static PfInt getInt(FunctionSymbol fs, IntegerDomain domain) {
        BigInteger value = PredefinedSemanticsFactory.getIntValue(fs, domain);
        if (value != null) {
            return new PfInt(domain, BigIntImmutable.create(value));
        } else {
            return null;
        }
    }

    public static PfInt getInt(BigIntImmutable value, IntegerDomain domain) {
        if (domain.inRange(value.getBigInt())) {
            return new PfInt(domain, value);
        } else {
            return null;
        }
    }

    public static final PfBoolean BOOLEAN_TRUE = PfBoolean.TRUE;
    public static final PfBoolean BOOLEAN_FALSE = PfBoolean.FALSE;
    public static final FunctionSymbol BOOLEAN_FS_TRUE = PfBoolean.FS_TRUE;
    public static final FunctionSymbol BOOLEAN_FS_FALSE = PfBoolean.FS_FALSE;
    public static final TRSFunctionApplication BOOLEAN_TERM_TRUE = PfBoolean.TERM_TRUE;
    public static final TRSFunctionApplication BOOLEAN_TERM_FALSE = PfBoolean.TERM_FALSE;

    public static Boolean getBoolValue(TRSTerm t) {
        if (PfBoolean.TERM_FALSE.equals(t)) {
            return false;
        } else if (PfBoolean.TERM_TRUE.equals(t)) {
            return true;
        } else {
            return null;
        }
    }

    public static Boolean getBoolValue(FunctionSymbol fs) {
        if (PfBoolean.FS_FALSE.equals(fs)) {
            return false;
        } else if (PfBoolean.FS_TRUE.equals(fs)) {
            return true;
        } else {
            return null;
        }
    }

    public static PfBoolean getBoolean(FunctionSymbol fs) {
        Boolean value = PredefinedSemanticsFactory.getBoolValue(fs);
        if (value != null) {
            return PredefinedSemanticsFactory.getBoolean(value);
        } else {
            return null;
        }
    }

    public static PfBoolean getBoolean(TRSTerm t) {
        Boolean value = PredefinedSemanticsFactory.getBoolValue(t);
        if (value != null) {
            return PredefinedSemanticsFactory.getBoolean(value);
        } else {
            return null;
        }
    }

    public static PfBoolean getBoolean(boolean value) {
        if (value) {
            return PfBoolean.TRUE;
        } else {
            return PfBoolean.FALSE;
        }
    }

    public static PredefinedFunction<? extends Domain> getFunction(Func func, ImmutableList<? extends Domain> domains) {
        synchronized (PredefinedSemanticsFactory.functions) {
            if (domains.size() != func.getArity()) {
                throw new IllegalArgumentException("arity does not match domain list");
            }
            Map<ImmutableList<? extends Domain>, PredefinedFunction<? extends Domain>> map = PredefinedSemanticsFactory.functions.get(func);
            if (map != null) {
                if (map.containsKey(domains)) {
                    return (PredefinedFunction<? extends Domain>) map.get(domains);
                }
            } else {
                map = new LinkedHashMap<ImmutableList<? extends Domain>, PredefinedFunction<? extends Domain>>();
                PredefinedSemanticsFactory.functions.put(func, map);
            }

            // really create function
            PredefinedFunction<? extends Domain> res = PredefinedSemanticsFactory.createFunction(func, domains);
            map.put(domains, res);
            return res;
        }
    }

    private static PredefinedFunction<? extends Domain> createFunction(Func func, ImmutableList<? extends Domain> domains) {
        switch (func) {
        case Add: {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfAdd(sameIntegerDomains);
            }
            break;
        }
        case Sub: {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfSub(sameIntegerDomains);
            }
            break;
        }
        case Mul: {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfMul(sameIntegerDomains);
            }
            break;
        }
        case Div: {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfDiv(sameIntegerDomains);
            }
            break;
        }
        case Mod: {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfMod(sameIntegerDomains);
            }
            break;
        }
        case UnaryMinus : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfUnaryMinus(sameIntegerDomains);
            }
            break;
        }
        case Cast: {
            ImmutableList<? extends IntegerDomain> allIntegerDomains = PredefinedSemanticsFactory.checkAllIntDomains(domains, false);
            if (allIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfCast(allIntegerDomains);
            }
            break;
        }
        case Eq : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfEq(sameIntegerDomains);
            }
            break;
        }
        case Neq : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfNeq(sameIntegerDomains);
            }
            break;
        }
        case Ge : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfGe(sameIntegerDomains);
            }
            break;
        }
        case Gt : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfGt(sameIntegerDomains);
            }
            break;
        }
        case Le : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfLe(sameIntegerDomains);
            }
            break;
        }
        case Lt : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfLt(sameIntegerDomains);
            }
            break;
        }
        case Bwand : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfBwand(sameIntegerDomains);
            }
            break;
        }
        case Bwor : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfBwor(sameIntegerDomains);
            }
            break;
        }
        case Bwxor : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfBwxor(sameIntegerDomains);
            }
            break;
        }
        case Bwnot : {
            ImmutableList<? extends IntegerDomain> sameIntegerDomains = PredefinedSemanticsFactory.checkSameIntDomains(domains);
            if (sameIntegerDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfBwnot(sameIntegerDomains);
            }
            break;
        }
        case Lor : {
            ImmutableList<BooleanDomain> booleanDomains = PredefinedSemanticsFactory.checkAllBooleanDomains(domains);
            if (booleanDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfLor(booleanDomains);
            }
            break;
        }
        case Land : {
            ImmutableList<BooleanDomain> booleanDomains = PredefinedSemanticsFactory.checkAllBooleanDomains(domains);
            if (booleanDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfLand(booleanDomains);
            }
            break;
        }
        case Lnot : {
            ImmutableList<BooleanDomain> booleanDomains = PredefinedSemanticsFactory.checkAllBooleanDomains(domains);
            if (booleanDomains != null) {
                return (PredefinedFunction<? extends Domain>) new PfLnot(booleanDomains);
            }
            break;
        }
        }
        return null;
    }

    static ImmutableList<? extends IntegerDomain> checkSameIntDomains(ImmutableList<? extends Domain> domains) {
        return PredefinedSemanticsFactory.checkAllIntDomains(domains, true);
    }

    static ImmutableList<? extends IntegerDomain> checkAllIntDomains(ImmutableList<? extends Domain> domains, boolean checkEquality) {
        if (!domains.isEmpty()) {
            ArrayList<IntegerDomain> res = new ArrayList<IntegerDomain>(domains.size());
            Domain domain = domains.get(0);
            if (domain instanceof IntegerDomain) {
                for (Domain dom : domains) {
                    if (!checkEquality || domain.equals(dom)) {
                        res.add((IntegerDomain) dom);
                    } else {
                        return null;
                    }
                }
                return ImmutableCreator.create(res);
            } else {
                return null;
            }
        } else {
            return ImmutableCreator.create(Collections.<IntegerDomain>emptyList());
        }
    }

    static ImmutableList<BooleanDomain> checkAllBooleanDomains(ImmutableList<? extends Domain> domains) {
        if (!domains.isEmpty()) {
            ArrayList<BooleanDomain> res = new ArrayList<BooleanDomain>(domains.size());
            for (Domain dom : domains) {
                if (DomainFactory.BOOLEAN.equals(dom)) {
                    res.add((BooleanDomain) dom);
                } else {
                    return null;
                }
            }
            return ImmutableCreator.create(res);
        } else {
            return ImmutableCreator.create(Collections.<BooleanDomain>emptyList());
        }
    }

    public static Collection<PredefinedFunction<? extends Domain>> getAllFunctions(Collection<? extends Domain> domains) {
        ArrayList<PredefinedFunction<? extends Domain>> res = new ArrayList<PredefinedFunction<? extends Domain>>();
        Collection<IntegerDomain> intDomains = new LinkedHashSet<IntegerDomain>();
        for (Domain domain : domains) {
            if (domain.isIntegerDomain()) {
                IntegerDomain intDomain = (IntegerDomain) domain;
                intDomains.add(intDomain);
                for (Func func : Func.values()) {
                    if (func.isIntFunction() && func != Func.Cast) {
                        ArrayList<IntegerDomain> doms = new ArrayList<IntegerDomain>(func.getArity());
                        for (int i = func.getArity() - 1; i>= 0; i--) {
                            doms.add(intDomain);
                        }
                        ImmutableList<? extends IntegerDomain> d = ImmutableCreator.create(doms);
                        PredefinedFunction<? extends Domain> preFunc = PredefinedSemanticsFactory.getFunction(func, d);
                        res.add(preFunc);
                    }
                }
            } else if (domain.isBooleanDomain()) {
                BooleanDomain boolDomain = (BooleanDomain) domain;
                for (Func func : Func.values()) {
                    if (func.isBooleanFunction()) {
                        ArrayList<BooleanDomain> doms = new ArrayList<BooleanDomain>(func.getArity());
                        for (int i = func.getArity() - 1; i>= 0; i--) {
                            doms.add(boolDomain);
                        }
                        ImmutableList<? extends BooleanDomain> d = ImmutableCreator.create(doms);
                        PredefinedFunction<? extends Domain> preFunc = PredefinedSemanticsFactory.getFunction(func, d);
                        res.add(preFunc);
                    }
                }
            }
        }
        for (IntegerDomain fromDomain : intDomains) {
            for (IntegerDomain toDomain : intDomains) {
                if (!fromDomain.equals(toDomain)) {
                    ArrayList<IntegerDomain> castDomains = new ArrayList<IntegerDomain>();
                    castDomains.add(fromDomain);
                    castDomains.add(toDomain);
                    ImmutableList<? extends Domain> d = ImmutableCreator.create(castDomains);
                    PredefinedFunction<? extends Domain> cast = PredefinedSemanticsFactory.getFunction(Func.Cast, d);
                    res.add(cast);
                }
            }
        }
        return res;
    }

}
