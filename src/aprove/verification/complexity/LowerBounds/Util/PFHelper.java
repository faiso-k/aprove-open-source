package aprove.verification.complexity.LowerBounds.Util;

import java.math.*;
import java.util.*;

import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.Transformations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Helper class that makes it easier to deal with terms with predefined functions.
 */
public class PFHelper {

    private final static IDPPredefinedMap map = IDPPredefinedMap.DEFAULT_MAP;

    public final static PfInt ZERO = IDPPredefinedMap.DEFAULT_MAP.getInt(BigIntImmutable.ZERO, DomainFactory.INTEGERS);
    public final static PfInt ONE = IDPPredefinedMap.DEFAULT_MAP.getInt(BigIntImmutable.ONE, DomainFactory.INTEGERS);
    public final static PfBoolean TRUE = IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue();
    public final static PfBoolean FALSE = IDPPredefinedMap.DEFAULT_MAP.getBooleanFalse();

    public final static FunctionSymbol AND = PFHelper.map.getSym(Func.Land, DomainFactory.BOOLEAN_BOOLEAN);
    public final static FunctionSymbol NOT = PFHelper.map.getSym(Func.Lnot, DomainFactory.BOOLEAN);

    public final static FunctionSymbol ADD = PFHelper.map.getSym(Func.Add, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol SUB = PFHelper.map.getSym(Func.Sub, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol MUL = PFHelper.map.getSym(Func.Mul, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol GE = PFHelper.map.getSym(Func.Ge, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol GT = PFHelper.map.getSym(Func.Gt, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol LE = PFHelper.map.getSym(Func.Le, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol LT = PFHelper.map.getSym(Func.Lt, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol EQ = PFHelper.map.getSym(Func.Eq, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol NEQ = PFHelper.map.getSym(Func.Neq, DomainFactory.INTEGER_INTEGER);
    public final static FunctionSymbol ITE = FunctionSymbol.create("ITE", 3);

    private final static Set<FunctionSymbol> arithmeticFunctionSymbols =
            new LinkedHashSet<>(Arrays.asList(new FunctionSymbol[] { PFHelper.ADD,
                                                                     PFHelper.MUL, }));

    private final static PredefinedFunction<?>[] predefinedFunctions =
            new PredefinedFunction<?>[] { PFHelper.map.getPredefinedFunction(PFHelper.GE),
                                          PFHelper.map.getPredefinedFunction(PFHelper.EQ), };

    private final static Set<Rule> predefinedRules = new LinkedHashSet<>();

    private final static Set<Rule> rulesForNeutralElements = new LinkedHashSet<>();

    static {
        TRSVariable x = TRSTerm.createVariable("x");
        TRSVariable y = TRSTerm.createVariable("y");

        TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(PFHelper.ITE, PFHelper.TRUE.getTerm(), x, y);
        TRSTerm rhs = x;
        PFHelper.predefinedRules.add(Rule.create(lhs, rhs));
        lhs = TRSTerm.createFunctionApplication(PFHelper.ITE, PFHelper.FALSE.getTerm(), x, y);
        rhs = y;
        PFHelper.predefinedRules.add(Rule.create(lhs, rhs));

        lhs = TRSTerm.createFunctionApplication(PFHelper.ADD, x, PFHelper.ZERO.getTerm());
        rhs = x;
        PFHelper.rulesForNeutralElements.add(Rule.create(lhs, rhs));
        lhs = TRSTerm.createFunctionApplication(PFHelper.ADD, PFHelper.ZERO.getTerm(), x);
        rhs = x;
        PFHelper.rulesForNeutralElements.add(Rule.create(lhs, rhs));
        lhs = TRSTerm.createFunctionApplication(PFHelper.MUL, x, PFHelper.ONE.getTerm());
        rhs = x;
        PFHelper.rulesForNeutralElements.add(Rule.create(lhs, rhs));
        lhs = TRSTerm.createFunctionApplication(PFHelper.MUL, PFHelper.ONE.getTerm(), x);
        rhs = x;
        PFHelper.rulesForNeutralElements.add(Rule.create(lhs, rhs));
    }

    public static boolean isInt(TRSTerm t) {
        if (t.isVariable()) {
            return false;
        } else {
            return IDPPredefinedMap.DEFAULT_MAP.isInt(((TRSFunctionApplication) t).getRootSymbol(), DomainFactory.INTEGERS);
        }
    }

    public static BigInteger toInt(TRSTerm t) {
        assert (PFHelper.isInt(t));
        FunctionSymbol symbol = ((TRSFunctionApplication) t).getRootSymbol();
        return IDPPredefinedMap.DEFAULT_MAP.getInt(symbol, DomainFactory.INTEGERS);
    }

    public static boolean isArithFunction(TRSTerm t) {
        if (!(t instanceof TRSFunctionApplication)) {
            return false;
        }
        FunctionSymbol rootSymbol = ((TRSFunctionApplication)t).getRootSymbol();
        return PFHelper.arithmeticFunctionSymbols.contains(rootSymbol);
    }

    public static boolean isArithExp(TRSTerm t) {
        return t.isVariable() || t.isConstant() || PFHelper.isInt(t) || PFHelper.isArithFunction(t);
    }

    public static TRSFunctionApplication toTerm(BigInteger i) {
        return IDPPredefinedMap.DEFAULT_MAP.getIntTerm(BigIntImmutable.create(i), DomainFactory.INTEGERS);
    }

    private TrsTypes types;

    public PFHelper(TrsTypes types) {
        this.types = types;
    }

    public TRSTerm normalize(TRSTerm t) {
        TRSTerm res = t;
        while (true) {
            TRSTerm newRes = this.rewrite(res);
            if (newRes == null) {
                return res;
            } else {
                res = newRes;
            }
        }
    }

    private TRSTerm rewrite(TRSTerm t) {
        for (Pair<Position, TRSTerm> p : t.getPositionsWithSubTerms()) {
            Position pos = p.x;
            TRSTerm s = p.y;
            TRSTerm newS;
            if (PFHelper.isArithFunction(s)) {
                TermToPolynomial termToPoly = new TermToPolynomial(this.types);
                SimplePolynomial poly = termToPoly.transform(s);
                Set<TRSFunctionApplication> constants = termToPoly.getConstants();
                newS = this.toNormalizedTerm(poly, constants);
            } else {
                newS = s;
            }
            if (s.equals(newS)) {
                newS = this.rewriteRoot(s);
            }
            if (!s.equals(newS)) {
                return t.replaceAt(pos, newS);
            }
        }
        return null;
    }

    private TRSTerm rewriteRoot(TRSTerm t) {
        if (t.isVariable()) {
            return t;
        }
        for (PredefinedFunction<?> predefinedFunction : PFHelper.predefinedFunctions) {
            if (predefinedFunction.canMatchPredefLhs(t, IDPPredefinedMap.DEFAULT_MAP)) {
                TRSTerm res = predefinedFunction.evaluate(((TRSFunctionApplication)t).getArguments());
                if (t.equals(res)) {
                    continue;
                }
                return res;
            }
        }
        for (Rule rule : PFHelper.predefinedRules) {
            if (rule.getLeft().matches(t)) {
                TRSSubstitution sigma = rule.getLeft().getMatcher(t);
                TRSTerm res = rule.getRight().applySubstitution(sigma);
                if (t.equals(res)) {
                    continue;
                }
                return res;
            }
        }
        return t;
    }

    /** orders the monomials and evaluates subexpressions like x+0 or y*1 */
    private TRSTerm toNormalizedTerm(SimplePolynomial poly, Set<TRSFunctionApplication> constants) {
        TRSTerm res = poly.toOrderedTerm();
        TRSSubstitution sigma = TRSSubstitution.EMPTY_SUBSTITUTION;
        for (TRSFunctionApplication c: constants) {
            sigma = sigma.compose(TRSSubstitution.create(TRSTerm.createVariable(c.getName()), c));
        }
        return this.removeNeutralElements(res.applySubstitution(sigma));
    }

    private TRSTerm removeNeutralElements(TRSTerm tArg) {
        TRSTerm t = tArg;
        boolean changed;
        do {
            changed = false;
            for (Pair<Position, TRSTerm> p: t.getPositionsWithSubTerms()) {
                Position pi = p.x;
                TRSTerm s = p.y;
                for (Rule r: PFHelper.rulesForNeutralElements) {
                    if (r.getLeft().matches(s)) {
                        TRSSubstitution sigma = r.getLeft().getMatcher(s);
                        t = t.replaceAt(pi, r.getRight().applySubstitution(sigma));
                        changed = true;
                    }
                }
            }
        } while (changed);
        return t;
    }

    /** @return a term resulting from s by replacing all int constants with fresh variables */
    public TRSTerm abstractFromIntConstants(TRSTerm s) {
        TRSTerm res = s;
        long next = 1;
        while (s.toString().contains("x" + next)) {
            next++;
        }
        for (Pair<Position, TRSTerm> e: res.getPositionsWithSubTerms()) {
            TRSTerm t = e.y;
            Position pos = e.x;
            if (PFHelper.isInt(t)) {
                res = res.replaceAt(pos, TRSTerm.createVariable("x" + next));
                next++;
            }
        }
        return res;
    }

    public static boolean isUnknownIntConstant(TRSTerm t, TrsTypes types) {
        return t.isConstant() && !PFHelper.isInt(t) && types.get(((TRSFunctionApplication)t).getRootSymbol()).equals(FunctionSymbolSimpleType.Nats);
    }

    public static TRSFunctionApplication getNeutralElement(FunctionSymbol symbol) {
        if (symbol == PFHelper.ADD) {
            return PFHelper.ZERO.getTerm();
        } else if (symbol == PFHelper.MUL) {
            return PFHelper.ONE.getTerm();
        } else {
            assert false;
            return null;
        }
    }

}
