package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Auxiliary stuff for dealing with terms in integer complexity problems.
 */
public class CpxIntTermHelper {

    private static final IDPPredefinedMap IDPMAP = IDPPredefinedMap.DEFAULT_MAP;

    public static FunctionSymbol getSym(final Func f, final Domain dom) {
        FunctionSymbol sym = CpxIntTermHelper.IDPMAP.getSym(f, dom);
        if (Globals.useAssertions) {
            assert sym != null;
        }
        return sym;
    }

    public static FunctionSymbol getIntegerSym(final Func f) {
        return CpxIntTermHelper.getSym(f, DomainFactory.INTEGERS);
    }

    public static FunctionSymbol getBooleanSym(final Func f) {
        return CpxIntTermHelper.getSym(f, DomainFactory.BOOLEAN);
    }

    public static final TRSFunctionApplication ZERO = (TRSFunctionApplication) CpxIntTermHelper.getInteger(BigIntImmutable.ZERO);
    public static final TRSFunctionApplication ONE = (TRSFunctionApplication) CpxIntTermHelper.getInteger(BigIntImmutable.ONE);

    public static final TRSFunctionApplication TRUE = TRSTerm.createFunctionApplication(CpxIntTermHelper.IDPMAP.getBooleanTrue().getSym());
    public static final TRSFunctionApplication FALSE = TRSTerm.createFunctionApplication(CpxIntTermHelper.IDPMAP.getBooleanFalse().getSym());

    public static final FunctionSymbol fLnot = CpxIntTermHelper.getBooleanSym(Func.Lnot);
    public static final FunctionSymbol fLand = CpxIntTermHelper.getBooleanSym(Func.Land);
    public static final FunctionSymbol fLor = CpxIntTermHelper.getBooleanSym(Func.Lor);
    public static final FunctionSymbol fAdd = CpxIntTermHelper.getIntegerSym(Func.Add);
    public static final FunctionSymbol fSub = CpxIntTermHelper.getIntegerSym(Func.Sub);
    public static final FunctionSymbol fMul = CpxIntTermHelper.getIntegerSym(Func.Mul);
    public static final FunctionSymbol fDiv = CpxIntTermHelper.getIntegerSym(Func.Div);
    public static final FunctionSymbol fMod = CpxIntTermHelper.getIntegerSym(Func.Mod);
    public static final FunctionSymbol fUnaryMinus = CpxIntTermHelper.getIntegerSym(Func.UnaryMinus);
    public static final FunctionSymbol fGt = CpxIntTermHelper.getIntegerSym(Func.Gt);
    public static final FunctionSymbol fGe = CpxIntTermHelper.getIntegerSym(Func.Ge);
    public static final FunctionSymbol fEq = CpxIntTermHelper.getIntegerSym(Func.Eq);
    public static final FunctionSymbol fNeq = CpxIntTermHelper.getIntegerSym(Func.Neq);
    public static final FunctionSymbol fLe = CpxIntTermHelper.getIntegerSym(Func.Le);
    public static final FunctionSymbol fLt = CpxIntTermHelper.getIntegerSym(Func.Lt);

    public static FunctionSymbol fCOM0 = CpxIntTermHelper.getComSymbol(0);
    public static FunctionSymbol fCOM1 = CpxIntTermHelper.getComSymbol(1);
    public static FunctionSymbol fCOM2 = CpxIntTermHelper.getComSymbol(2);

    public static final ImmutableSet<FunctionSymbol> polySyms;
    static {
        Set<FunctionSymbol> syms = new LinkedHashSet<>();
        syms.add(CpxIntTermHelper.fAdd);
        syms.add(CpxIntTermHelper.fMul);
        syms.add(CpxIntTermHelper.fSub);
        syms.add(CpxIntTermHelper.fUnaryMinus);
        polySyms = ImmutableCreator.create(syms);
    }

    public static boolean isConstraintTerm(final TRSTerm t) {
        if (t.isVariable()) {
            return true;
        }

        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();

        if (!CpxIntTermHelper.IDPMAP.isPredefined(fs)) {
            return false;
        }

        for (TRSTerm t2 : fa.getArguments()) {
            if (!CpxIntTermHelper.isConstraintTerm(t2)) {
                return false;
            }
        }
        return true;
    }

    public static final String ComPrefix = "Com_";

    public static boolean isComSymbol(final FunctionSymbol comn) {
        return comn.getName().equals(CpxIntTermHelper.ComPrefix + comn.getArity());
    }

    public static FunctionSymbol getComSymbol(final int arity) {
        return FunctionSymbol.create(CpxIntTermHelper.ComPrefix + arity, arity);
    }

    public static TRSTerm getInteger(final BigIntImmutable i) {
        return CpxIntTermHelper.IDPMAP.getIntTerm(i, DomainFactory.INTEGERS);
    }

    /**
     * Render a SimplePolynomial into a Term.
     * @param pol
     * @return
     */
    public static TRSTerm fromSimplePolynomial(final SimplePolynomial pol) {
        TRSTerm result = null;
        for (Entry<IndefinitePart, BigInteger> smon : pol.getSimpleMonomials().entrySet()) {
            IndefinitePart indef = smon.getKey();
            BigInteger coeff = smon.getValue();
            TRSTerm monTerm;
            TRSTerm coeffPart = CpxIntTermHelper.IDPMAP.getIntTerm(BigIntImmutable.create(coeff), DomainFactory.INTEGERS);
            TRSTerm indefPart = null;
            for (Entry<String, Integer> e : indef.getExponents().entrySet()) {
                TRSTerm v = TRSTerm.createVariable(e.getKey());
                int exp = e.getValue();
                for (int i = 0; i < exp; ++i) {
                    if (indefPart == null) {
                        indefPart = v;
                    } else {
                        indefPart = TRSTerm.createFunctionApplication(CpxIntTermHelper.fMul, v, indefPart);
                    }
                }
            }
            if (indef.isEmpty()) {
                monTerm = coeffPart;
            } else if (coeff.equals(BigInteger.ONE)) {
                monTerm = indefPart;
            } else {
                monTerm = TRSTerm.createFunctionApplication(CpxIntTermHelper.fMul, coeffPart, indefPart);
            }
            if (result == null) {
                result = monTerm;
            } else {
                result = TRSTerm.createFunctionApplication(CpxIntTermHelper.fAdd, result, monTerm);
            }
        }
        if (result == null) {
            return CpxIntTermHelper.ZERO;
        }
        return result;
    }

    public static TRSFunctionApplication filterDefinedProperSubterms(
        final TRSFunctionApplication t,
        final Set<FunctionSymbol> defs,
        final FreshNameGenerator fng)
    {
        ArrayList<TRSTerm> args = new ArrayList<>();
        for (TRSTerm sub : t.getArguments()) {
            if (!sub.isVariable()) {
                TRSFunctionApplication subFA = (TRSFunctionApplication) sub;
                if (defs.contains(subFA.getRootSymbol())) {
                    args.add(TRSTerm.createVariable(fng.getFreshName("f", false)));
                } else {
                    args.add(CpxIntTermHelper.filterDefinedProperSubterms(subFA, defs, fng));
                }
            } else {
                args.add(sub);
            }
        }
        return TRSTerm.createFunctionApplication(t.getRootSymbol(), args);
    }

    public static boolean isIntegerTerm(final TRSTerm t) {
        if (t.isVariable()) {
            return true;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        if (CpxIntTermHelper.IDPMAP.isInt(fs, DomainFactory.INTEGERS)) {
            return true;
        }
        PredefinedFunction<? extends Domain> predef = CpxIntTermHelper.IDPMAP.getPredefinedFunction(fs);
        if (predef == null || !predef.isArithmetic()) {
            return false;
        }
        for (TRSTerm subt : fa.getArguments()) {
            if (!CpxIntTermHelper.isIntegerTerm(subt)) {
                return false;
            }
        }
        return true;
    }

    public static BigInteger getIntegerValue(final TRSFunctionApplication fa) {
        FunctionSymbol fs = fa.getRootSymbol();
        return CpxIntTermHelper.IDPMAP.getInt(fs, DomainFactory.INTEGERS);
    }

    private static boolean isBooleanTerm(final TRSTerm t) {
        if (t.isVariable()) {
            return false;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        if (CpxIntTermHelper.IDPMAP.isBooleanFalse(fs) || CpxIntTermHelper.IDPMAP.isBooleanTrue(fs)) {
            return true;
        }
        PredefinedFunction<? extends Domain> predef = CpxIntTermHelper.IDPMAP.getPredefinedFunction(fs);
        if (predef == null) {
            return false;
        }
        if (predef.isRelation()) {
            for (TRSTerm subterm : fa.getArguments()) {
                if (!CpxIntTermHelper.isIntegerTerm(subterm)) {
                    return false;
                }
            }
            return true;
        } else if (predef.isBoolean()) {
            for (TRSTerm subterm : fa.getArguments()) {
                if (!CpxIntTermHelper.isBooleanTerm(subterm)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    public static TRSTerm createLnot(final TRSTerm t) {
        return TRSTerm.createFunctionApplication(CpxIntTermHelper.fLnot, t);
    }

    public static TRSTerm createLandNullIsTrue(final TRSTerm t1, final TRSTerm t2) {
        if (t1 == null) {
            if (t2 == null) {
                return CpxIntTermHelper.TRUE;
            }
            return t2;
        }
        if (t2 == null) {
            return t1;
        }
        return TRSTerm.createFunctionApplication(CpxIntTermHelper.fLand, t1, t2);
    }

    public static Set<IGeneralizedRule> splitOffBooleanExpressions(final IGeneralizedRule rule) {
        Deque<IGeneralizedRule> check = new ArrayDeque<>();
        check.add(rule);
        Set<IGeneralizedRule> result = new LinkedHashSet<>();

        // all boolean expression on the rhs are replaced by either TRUE (FALSE)
        // and the
        // (negated) expression is moved into the constraints
        check: while (!check.isEmpty()) {
            IGeneralizedRule nextRule = check.pop();
            TRSTerm rhs = nextRule.getRight();
            for (Position p : rhs.getPositions()) {
                TRSTerm subterm = rhs.getSubterm(p);
                if (CpxIntTermHelper.isExtractableBooleanTerm(subterm)) {
                    TRSFunctionApplication lhs = nextRule.getLeft();
                    TRSTerm constraint = nextRule.getCondTerm();
                    check.push(IGeneralizedRule.create(
                        lhs,
                        nextRule.getRight().replaceAt(p, CpxIntTermHelper.TRUE),
                        CpxIntTermHelper.createLandNullIsTrue(subterm, constraint)));
                    check.push(IGeneralizedRule.create(
                        lhs,
                        nextRule.getRight().replaceAt(p, CpxIntTermHelper.FALSE),
                        CpxIntTermHelper.createLandNullIsTrue(CpxIntTermHelper.createLnot(subterm), constraint)));
                    continue check;
                }
            }
            result.add(nextRule);
        }
        return result;
    }

    private static boolean isExtractableBooleanTerm(final TRSTerm t) {
        if (CpxIntTermHelper.TRUE.equals(t) || CpxIntTermHelper.FALSE.equals(t)) {
            return false;
        }
        return CpxIntTermHelper.isBooleanTerm(t);
    }

    public static TRSTerm splitOffIntegerExpressions(
        final TRSTerm t,
        final FreshNameGenerator fng,
        final LinkedHashSet<Constraint> constraintAkk) throws NoConstraintTermException
    {
        if (t.isVariable()) {
            return t;
        }
        if (CpxIntTermHelper.isIntegerTerm(t)) {
            TRSVariable fresh = TRSTerm.createVariable(fng.getFreshName("z", false));
            constraintAkk.add(Constraint.create(TRSTerm.createFunctionApplication(CpxIntTermHelper.fGe, fresh, t)));
            constraintAkk.add(Constraint.create(TRSTerm.createFunctionApplication(CpxIntTermHelper.fLe, fresh, t)));
            return fresh;
        }

        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        ArrayList<TRSTerm> args = new ArrayList<>();
        for (TRSTerm subt : fa.getArguments()) {
            args.add(CpxIntTermHelper.splitOffIntegerExpressions(subt, fng, constraintAkk));
        }
        return TRSTerm.createFunctionApplication(fa.getRootSymbol(), args);
    }

    public static LinkedHashSet<CpxIntTupleRule> createWithoutCompounds(final Set<IGeneralizedRule> rules)
        throws NoValidCpxIntTupleRuleException,
            NoConstraintTermException
    {
        Set<FunctionSymbol> defs = new LinkedHashSet<>();

        for (IGeneralizedRule rule : rules) {
            defs.add(rule.getLeft().getRootSymbol());
        }

        LinkedHashSet<CpxIntTupleRule> crules = new LinkedHashSet<>();
        for (IGeneralizedRule rule : rules) {
            FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
            Set<String> varNames = new LinkedHashSet<>();
            for (TRSVariable v : rule.getVariables()) {
                varNames.add(v.getName());
            }
            // we need to avoid clashes with variable names in the constraints
            if (rule.getCondTerm() != null) {
                for (TRSVariable v : rule.getCondTerm().getVariables()) {
                    varNames.add(v.getName());
                }
            }
            fng.lockNames(varNames);
            // iterate over all function calls in the rhs of rule
            ArrayList<TRSFunctionApplication> args = new ArrayList<>();

            LinkedHashSet<Constraint> additionalConstraints = new LinkedHashSet<>();
            TRSTerm rhsWithoutArithmetic = CpxIntTermHelper.splitOffIntegerExpressions(rule.getRight(), fng, additionalConstraints);

            for (TRSTerm t : rhsWithoutArithmetic.getSubTerms()) {
                if (t.isVariable()) {
                    continue;
                }
                TRSFunctionApplication fa = (TRSFunctionApplication) t;
                if (defs.contains(fa.getRootSymbol())) {
                    args.add(CpxIntTermHelper.filterDefinedProperSubterms(fa, defs, fng));
                }
            }
            FunctionSymbol com = CpxIntTermHelper.getComSymbol(args.size());
            IGeneralizedRule comRule =
                IGeneralizedRule.create(rule.getLeft(), TRSTerm.createFunctionApplication(com, args), rule.getCondTerm());

            ImmutableLinkedHashSet<Constraint> immConstraints = ImmutableCreator.create(additionalConstraints);
            Set<IGeneralizedRule> splits = CpxIntTermHelper.splitOffBooleanExpressions(comRule);
            for (IGeneralizedRule irule : splits) {

                LinkedHashSet<CpxIntTupleRule> conjunctiveRules;
                conjunctiveRules = CpxIntTupleRule.createRules(irule, immConstraints);
                crules.addAll(conjunctiveRules);
            }
        }

        return crules;
    }

    private static Set<LinkedHashSet<Constraint>> genClause(final LinkedHashSet<Constraint> clause) {
        Set<LinkedHashSet<Constraint>> dnf = new LinkedHashSet<>();
        dnf.add(clause);
        return dnf;
    }

    /**
     * Given a {@link TRSTerm} representing a constraint, return its representation
     * as a disjunctive normal form (a {@link Set} of {@link Set}s of
     * {@link Constraint}), or throw a {@link NotAPropositionalFormulaException}
     * if no such representation could be constructed.
     * @param constrTerm
     * @return
     * @throws NotAPropositionalFormulaException
     * @throws NoConstraintTermException
     */
    public static Set<LinkedHashSet<Constraint>> computeDNF(final TRSFunctionApplication constrTerm)
        throws NoConstraintTermException
    {
        if (CpxIntTermHelper.TRUE.equals(constrTerm)) {
            Set<LinkedHashSet<Constraint>> True = new LinkedHashSet<>();
            True.add(new LinkedHashSet<Constraint>());
            return True;
        }
        if (CpxIntTermHelper.FALSE.equals(constrTerm)) {
            Set<LinkedHashSet<Constraint>> False = new LinkedHashSet<>();
            return False;
        }
        FunctionSymbol fs = constrTerm.getRootSymbol();
        PredefinedFunction<? extends Domain> function = CpxIntTermHelper.IDPMAP.getPredefinedFunction(fs);
        if (!function.isBoolean() && !function.isRelation()) {
            throw new NoConstraintTermException(constrTerm);
        }
        Func func = function.getFunc();
        Set<LinkedHashSet<Constraint>> dnf;
        LinkedHashSet<Constraint> clause;

        switch (func) {
        // atoms
        case Eq:
            clause = new LinkedHashSet<>();
            clause.add(Constraint.create(TRSTerm.createFunctionApplication(
                CpxIntTermHelper.fGe,
                constrTerm.getArgument(0),
                constrTerm.getArgument(1))));
            clause.add(Constraint.create(TRSTerm.createFunctionApplication(
                CpxIntTermHelper.fLe,
                constrTerm.getArgument(0),
                constrTerm.getArgument(1))));
            return CpxIntTermHelper.genClause(clause);
        case Neq: {
            LinkedHashSet<Constraint> clause1 = new LinkedHashSet<>();
            clause1.add(Constraint.create(TRSTerm.createFunctionApplication(
                CpxIntTermHelper.fGt,
                constrTerm.getArgument(0),
                constrTerm.getArgument(1))));
            LinkedHashSet<Constraint> clause2 = new LinkedHashSet<>();
            clause2.add(Constraint.create(TRSTerm.createFunctionApplication(
                CpxIntTermHelper.fLt,
                constrTerm.getArgument(0),
                constrTerm.getArgument(1))));
            Set<LinkedHashSet<Constraint>> res = new LinkedHashSet<>();
            res.add(clause1);
            res.add(clause2);
            return res;
        }
        case Ge:
        case Gt:
        case Le:
        case Lt:
            clause = new LinkedHashSet<>();
            clause.add(Constraint.create(TRSTerm.createFunctionApplication(
                fs,
                constrTerm.getArgument(0),
                constrTerm.getArgument(1))));
            return CpxIntTermHelper.genClause(clause);
            // logical operators
        case Lnot:
            if (constrTerm.getArgument(0).isVariable()) {
                throw new NoConstraintTermException(constrTerm);
            }
            Set<LinkedHashSet<Constraint>> sub = CpxIntTermHelper.computeDNF((TRSFunctionApplication) constrTerm.getArgument(0));
            dnf = new LinkedHashSet<>();
            dnf.add(new LinkedHashSet<Constraint>());
            for (Set<Constraint> subclause : sub) {
                Set<LinkedHashSet<Constraint>> nextdnf = new LinkedHashSet<>();
                for (Constraint ineq : subclause) {
                    Constraint neg = ineq.negate();
                    for (Set<Constraint> subcl : dnf) {
                        LinkedHashSet<Constraint> cl = new LinkedHashSet<>();
                        cl.addAll(subcl);
                        cl.add(neg);
                        nextdnf.add(cl);
                    }
                }
                dnf = nextdnf;
            }
            return dnf;
        case Land:
        case Lor:
            if (constrTerm.getArgument(0).isVariable() || constrTerm.getArgument(1).isVariable()) {
                throw new NoConstraintTermException(constrTerm);
            }
            Set<LinkedHashSet<Constraint>> left = CpxIntTermHelper.computeDNF((TRSFunctionApplication) constrTerm.getArgument(0));
            Set<LinkedHashSet<Constraint>> right = CpxIntTermHelper.computeDNF((TRSFunctionApplication) constrTerm.getArgument(1));
            switch (func) {
            case Land:
                // de morgan
                dnf = new LinkedHashSet<>();
                for (Set<Constraint> a : left) {
                    for (Set<Constraint> b : right) {
                        clause = new LinkedHashSet<>();
                        clause.addAll(a);
                        clause.addAll(b);
                        dnf.add(clause);
                    }
                }
                return dnf;
            case Lor:
                dnf = new LinkedHashSet<>();
                dnf.addAll(left);
                dnf.addAll(right);
                return dnf;
            default:
                // should be unreachable
                throw new NoConstraintTermException(constrTerm);
            }
        default:
            throw new NoConstraintTermException(constrTerm);
        }
    }

    public static TRSFunctionApplication addTerms(final TRSTerm a, final TRSTerm b) {
        return TRSTerm.createFunctionApplication(CpxIntTermHelper.fAdd, a, b);
    }

    public static TRSFunctionApplication subTerms(final TRSTerm a, final TRSTerm b) {
        return TRSTerm.createFunctionApplication(CpxIntTermHelper.fSub, a, b);
    }

    public static TRSFunctionApplication mulTerms(final TRSTerm a, final TRSTerm b) {
        return TRSTerm.createFunctionApplication(CpxIntTermHelper.fMul, a, b);
    }

    public static SimplePolynomial toSimplePolynomial(final TRSTerm t) throws NotRepresentableAsPolynomialException {
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable) t;
            return SimplePolynomial.create(v.getName());
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        BigInteger intValue = CpxIntTermHelper.getIntegerValue(fa);
        if (intValue != null) {
            return SimplePolynomial.create(intValue);
        }
        if (CpxIntTermHelper.IDPMAP.isAdd(fs)) {
            SimplePolynomial left = CpxIntTermHelper.toSimplePolynomial(fa.getArgument(0));
            SimplePolynomial right = CpxIntTermHelper.toSimplePolynomial(fa.getArgument(1));
            return left.plus(right);
        }
        if (CpxIntTermHelper.IDPMAP.isMul(fs)) {
            SimplePolynomial left = CpxIntTermHelper.toSimplePolynomial(fa.getArgument(0));
            SimplePolynomial right = CpxIntTermHelper.toSimplePolynomial(fa.getArgument(1));
            return left.times(right);
        }
        if (CpxIntTermHelper.IDPMAP.isSub(fs)) {
            SimplePolynomial left = CpxIntTermHelper.toSimplePolynomial(fa.getArgument(0));
            SimplePolynomial right = CpxIntTermHelper.toSimplePolynomial(fa.getArgument(1));
            return left.minus(right);
        }
        if (CpxIntTermHelper.IDPMAP.isUnaryMinus(fs)) {
            return CpxIntTermHelper.toSimplePolynomial(fa.getArgument(0)).negate();
        }
        throw new NotRepresentableAsPolynomialException();
    }

    public static String exportTerm(TRSTerm t, Export_Util eu) {
        LinkedHashSet<TRSVariable> freeVars = new LinkedHashSet<>();
        StringBuilder sb = new StringBuilder();
        IDPExport.exportTermWithPrec(t, 0, eu, freeVars, CpxIntTermHelper.IDPMAP, sb);
        return sb.toString();
    }

    public static TRSFunctionApplication createCom(TRSFunctionApplication... ts) {
        return CpxIntTermHelper.createCom(Arrays.asList(ts));
    }

    public static TRSFunctionApplication createCom(Collection<TRSFunctionApplication> ts) {
        ArrayList<TRSTerm> args = new ArrayList<>();
        args.addAll(ts);
        return TRSTerm.createFunctionApplication(CpxIntTermHelper.getComSymbol(args.size()), ImmutableCreator.create(args));
    }
}
