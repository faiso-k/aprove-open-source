package aprove.verification.dpframework.CLSProblem.Utility;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Replaces CLS symbols in a Term by ITRS symbols.
 *
 * <p>
 * The set of supported CLS symbols is currently the set of function symbols
 * supported by the CLSToITRSProcessor.
 * </p>
 *
 * <p>
 * Applying this class to lhs and rhs of a Rule is not sufficient for a correct
 * CLS to ITRS conversion!
 * </p>
 */
public class ITRSIntTermVisitor extends TermVisitor {

    private final static IntegerDomain DOMAIN =
        DomainFactory.INTEGERS;

    private final static ImmutableList<IntegerDomain> DOMAIN_DOMAIN;
    static {
        ArrayList<IntegerDomain> domains2 = new ArrayList<IntegerDomain>(2);
        domains2.add(ITRSIntTermVisitor.DOMAIN);
        domains2.add(ITRSIntTermVisitor.DOMAIN);
        DOMAIN_DOMAIN = ImmutableCreator.create(domains2);
    }

    private final static TRSTerm zero =
        PredefinedSemanticsFactory.getInt(BigIntImmutable.ZERO, ITRSIntTermVisitor.DOMAIN).getTerm();

    private final static Map<FunctionSymbol, FunctionSymbol> CLS2ITRS;
    static {

        ArrayList<IntegerDomain> domain = new ArrayList<IntegerDomain>(1);
        domain.add(ITRSIntTermVisitor.DOMAIN);
        ImmutableList<IntegerDomain> intDom = ImmutableCreator.create(domain);

        CLS2ITRS = new HashMap<FunctionSymbol, FunctionSymbol>();
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Add.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Add, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Sub.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Sub, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Mul.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Mul, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Div.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Div, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Neg.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.UnaryMinus, intDom));

        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Not.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Lnot, DomainFactory.BOOLEAN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.And.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Land, DomainFactory.BOOLEAN_BOOLEAN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Or.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Lor, DomainFactory.BOOLEAN_BOOLEAN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Clt.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Lt, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Cle.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Le, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Ceq.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Eq, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Cge.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Ge, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        ITRSIntTermVisitor.CLS2ITRS.put(aprove.verification.dpframework.CLSProblem.Utility.PredefinedFunctions.Cgt.getSym(),
                IDPPredefinedMap.DEFAULT_MAP.getSym(PredefinedFunction.Func.Gt, ITRSIntTermVisitor.DOMAIN_DOMAIN));
        // check that we got a semantic for every function
        if (Globals.useAssertions) {
            for (Map.Entry<FunctionSymbol, FunctionSymbol> entry : ITRSIntTermVisitor.CLS2ITRS.entrySet()) {
                assert entry.getValue() != null : "no ITRS semantics for " + entry.getKey();
            }
        }

    }

    @Override
    public TRSTerm caseInFunctionApplication(TRSFunctionApplication fa) {
        FunctionSymbol sym = fa.getRootSymbol();
        if (PredefinedHelper.isInt(sym)) {
            BigInteger val = PredefinedHelper.toInteger(sym);
            return PredefinedSemanticsFactory.getIntTerm(BigIntImmutable.create(val), ITRSIntTermVisitor.DOMAIN);
        }
        return null;
    }

    @Override
    public TRSTerm caseInVariable(TRSVariable v) {
        return null;
    }

    @Override
    public TRSTerm caseOutFunctionApplication(TRSFunctionApplication fa) {
        FunctionSymbol sym = ITRSIntTermVisitor.CLS2ITRS.get(fa.getRootSymbol());
        if (sym == null) {
            return null;
        }
        PredefinedFunction<? extends Domain> pf = IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(sym);
        ImmutableList<? extends TRSTerm> args = fa.getArguments();
        if (pf.isBoolean()) {
            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
            for (TRSTerm arg : args) {
                if (!(arg instanceof TRSVariable)) {
                    FunctionSymbol argFs = ((TRSFunctionApplication)arg).getRootSymbol();
                    PredefinedFunction<? extends Domain> argPf =
                        IDPPredefinedMap.DEFAULT_MAP.getPredefinedFunction(argFs);
                    if (argPf != null && (argPf.isBoolean() || argPf.isRelation())) {
                        // ok
                    } else if (IDPPredefinedMap.DEFAULT_MAP.isInt(argFs, ITRSIntTermVisitor.DOMAIN)) {
                        /* change constants to true/false*/
                        BigInteger i = IDPPredefinedMap.DEFAULT_MAP.getInt(argFs, ITRSIntTermVisitor.DOMAIN);
                        if (i.equals(BigInteger.ZERO)) {
                            arg = PredefinedSemanticsFactory.BOOLEAN_TERM_FALSE;
                        } else {
                            arg = PredefinedSemanticsFactory.BOOLEAN_TERM_TRUE;
                        }
                    } else {
                        /* change non-constant integers to arg != 0 */
                        arg =
                            TRSTerm.createFunctionApplication(
                                IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Neq, ITRSIntTermVisitor.DOMAIN_DOMAIN),
                                ITRSIntTermVisitor.zero,
                                arg
                            );
                    }
                }
                newArgs.add(arg);
            }
            return TRSTerm.createFunctionApplication(sym,
                    ImmutableCreator.create(newArgs));
        } else {
            return TRSTerm.createFunctionApplication(sym, fa.getArguments());
        }
    }
}
