package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT;

import java.math.*;
import java.util.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Utils.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author marinag
 * Translates terms into SimplePolynomial, SimplePolyConstraint, PolyConstraintsSystem
 */
public abstract class TermTools {

    /**
     * @param t term
     * @return the corresponding SimplePolynomial
     * @throws UnsupportedException in case the term t contains function symbols other than integers and the operators { +, - , * }.
     */
    public static SimplePolynomial getSimplePolynomial(final TRSTerm t) throws UnsupportedException {
        if (t instanceof TRSVariable) {
            return SimplePolynomial.create(t.getName());
        }
        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);


        if (fSymb.getArity() == 0) {
            final BigInteger value = Function.getBigInteger(fSymb);

            if (value != null) {
                return SimplePolynomial.create(value);
            }
            throw new UnsupportedException(t.toString() + " has no polynomial form");
        }

        if (f == null) {
            throw new UnsupportedException(t.toString() + " has no polynomial form");
        }
        switch (f) {
        case ADD:
        case SUB:
        case MUL:
            final SimplePolynomial a = TermTools.getSimplePolynomial(fApp.getArgument(0));
            final SimplePolynomial b = TermTools.getSimplePolynomial(fApp.getArgument(1));

            switch (f) {
            case ADD:
                return a.plus(b);
            case SUB:
                return a.minus(b);
            case MUL:
                return a.times(b);
            }

            throw new RuntimeException();

        case UMINUS:
            return TermTools.getSimplePolynomial(fApp.getArgument(0)).negate();
        default:
            throw new UnsupportedException(t.toString() + " has no polynomial form");
        }
    }

    /**
     * @param t term
     * @return equivalent term without { !, != }
     * @throws UnsupportedException in case of negation of function application other than { < ,<=, ==, > , >= ,!= } or of variables
     */
    private static TRSTerm removeNegation(final TRSTerm t) throws UnsupportedException {
        if (t instanceof TRSVariable) {
            return t;
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        final ArrayList<TRSTerm> nfArgs = new ArrayList<>(fSymb.getArity());

        for (final TRSTerm arg : fApp.getArguments()) {
            nfArgs.add(TermTools.removeNegation(arg));
        }

        if (f != null) {
            switch (f) {
            case LNOT:
                return TermTools.negate(nfArgs.get(0));
            case NEQ:
                final TRSTerm a = nfArgs.get(0);
                final TRSTerm b = nfArgs.get(1);

                if (a.equals(b)) {
                    return TermTools.FALSE;
                }

                final TRSTerm t1 = ToolBox.buildGt(a, b);
                final TRSTerm t2 = ToolBox.buildGt(b, a);

                return TermTools.buildOr(t1, t2);
            }
        }


        return TRSTerm.createFunctionApplication(fSymb, nfArgs);
    }

    /**
     * @param t term
     * @return corresponding negated term, without { !, <> }
     */
    public static TRSTerm negate(final TRSTerm t) throws UnsupportedException {
        if (t instanceof TRSVariable) {
            throw new UnsupportedException("The variable " + t.toString() + " has no negated form");
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        switch (f) {
        case TRUE:
            return ToolBox.buildFalse();
        case FALSE:
            return ToolBox.buildTrue();

        case CAST:
            return TermTools.negate(fApp.getArgument(0));

        case GT:
        case GE:
        case EQ:
        case LE:
        case LT:
        case NEQ:
        case LAND:
        case LOR: {
            final TRSTerm a = fApp.getArgument(0);
            final TRSTerm b = fApp.getArgument(1);




            switch (f) {
            case GT:
                return ToolBox.buildLe(a, b);
            case GE:
                return ToolBox.buildLt(a, b);
            case EQ:
                return ToolBox.buildOr(ToolBox.buildLt(a, b), ToolBox.buildGt(a, b));
            case LE:
                return ToolBox.buildGt(a, b);
            case LT:
                return ToolBox.buildGe(a, b);
            case NEQ:
                return ToolBox.buildEq(a, b);
            case LAND:
                return TermTools.buildOr(TermTools.negate(a), TermTools.negate(b));
            case LOR:
                return TermTools.buildAnd(TermTools.negate(a), TermTools.negate(b));
            }
        }
        break;

        case LNOT:
            return fApp.getArgument(0);
        }

        throw new UnsupportedException("The term " + t.toString() + " has no negated form");

    }


    public static List<TRSTerm> getAtomsWithNegation(final TRSTerm t) throws UnsupportedException {
        if ((t instanceof TRSVariable)) {
            throw new UnsupportedException("The term " + t.toString() + " can not be transfered to general atoms list");
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fs = fApp.getRootSymbol();

        final List<TRSTerm> atoms = new ArrayList<>();

        if (TermTools.PREDEFINED.isLand(fs) || TermTools.PREDEFINED.isLor(fs)) {
            atoms.addAll(TermTools.getAtoms(fApp.getArgument(0)));
            atoms.addAll(TermTools.getAtoms(fApp.getArgument(1)));
        } else {
            atoms.add(t);
        }

        return atoms;
    }



    public static List<TRSTerm> getAtoms(final TRSTerm t) throws UnsupportedException {
        if ((t instanceof TRSVariable) || (TermTools.PREDEFINED.isLor(((TRSFunctionApplication) t).getRootSymbol()))) {
            throw new UnsupportedException("The term " + t.toString() + " can not be transfered to atoms list");
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fs = fApp.getRootSymbol();

        final List<TRSTerm> atoms = new ArrayList<>();

        if (TermTools.PREDEFINED.isLand(fs)) {
            atoms.addAll(TermTools.getAtoms(fApp.getArgument(0)));
            atoms.addAll(TermTools.getAtoms(fApp.getArgument(1)));
        } else {
            atoms.add(t);
        }

        return atoms;
    }

    /**
     * @param t
     * @return set of corresponding conjunctive clauses
     */
    public static List<TRSTerm> getDNF(final TRSTerm t) throws UnsupportedException {
        final TRSTerm eval = TermTools.evaluate(t);
        final TRSTerm nfT = TermTools.removeNegation(eval);
        return new ArrayList<>(TermTools.getDNFnNeg(nfT));
    }

    /**
     * @param t
     * @return set of corresponding conjunctive clauses
     */
    public static List<TRSTerm> getDNFwN(final TRSTerm t) throws UnsupportedException {
        final TRSTerm eval = TermTools.evaluate(t);
        final TRSTerm nfT = TermTools.removeNegationNonAtoms(eval);
        return new ArrayList<>(TermTools.getDNFwNeq(nfT));
    }

    private static TRSTerm removeNegationNonAtoms(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return t;
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        final ArrayList<TRSTerm> nfArgs = new ArrayList<>(fSymb.getArity());

        for (final TRSTerm arg : fApp.getArguments()) {
            nfArgs.add(TermTools.removeNegationNonAtoms(arg));
        }

        if (f != null) {
            switch (f) {
            case LNOT:
                if (!TermTools.isAtomWNeg(t)) {
                    try {
                        return TermTools.negate(nfArgs.get(0));
                    } catch (final UnsupportedException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }
                }

            }
        }

        return TRSTerm.createFunctionApplication(fSymb, nfArgs);
    }

    private static boolean isAtomWNeg(final TRSTerm t) {
        if (TermTools.isAtom(t)) {
            return true;
        }

        if (t instanceof TRSVariable) {
            return false;
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        if (fSymb.getArity() == 0) {
            return false;
        }

        switch (f) {

        case LNOT:
            return TermTools.isAtom(fApp.getArgument(0));
        }

        return false;
    }

    private static boolean isAtom(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return false;
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        if (fSymb.getArity() == 0) {
            return false;
        }

        switch (f) {
        case GT:
        case GE:
        case EQ:
        case LE:
        case LT:
        case NEQ:
            return true;
        }

        return false;
    }

    public static Set<TRSTerm> getDNFwNeq(final TRSTerm t) throws UnsupportedException {
        if (t instanceof TRSVariable) {
            throw new UnsupportedException("The variable " + t.toString() + " has no DNF form");
        }

        final Set<TRSTerm> result = new HashSet<>();

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        switch (f) {
        case LAND:
        case LOR:
            final Set<TRSTerm> res1 = TermTools.getDNFwNeq(fApp.getArgument(0));
            final Set<TRSTerm> res2 = TermTools.getDNFwNeq(fApp.getArgument(1));

            if (f.equals(Function.LAND)) {
                for (final TRSTerm t1 : res1) {
                    for (final TRSTerm t2 : res2) {
                        result.add(TermTools.buildAnd(t1, t2));
                    }
                }
            } else {
                result.addAll(res1);
                result.addAll(res2);
            }

            return result;

        }

        result.add(t);

        return result;
    }

    /**
     * @param t term without without { !, != }
     * @return set of corresponding conjunctive clauses
     * @throws UnsupportedException in case the term t contains { !, != } or function application other than { < ,<=, ==, > , >= ,!= } or of variables
     */
    private static Set<TRSTerm> getDNFnNeg(final TRSTerm t) throws UnsupportedException {
        if (t instanceof TRSVariable) {
            throw new UnsupportedException("The variable " + t.toString() + " has no DNF form");
        }

        final Set<TRSTerm> result = new HashSet<>();

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        switch (f) {
        case LAND:
        case LOR:
            final Set<TRSTerm> res1 = TermTools.getDNFnNeg(fApp.getArgument(0));
            final Set<TRSTerm> res2 = TermTools.getDNFnNeg(fApp.getArgument(1));

            if (f.equals(Function.LAND)) {
                for (final TRSTerm t1 : res1) {
                    for (final TRSTerm t2 : res2) {
                        result.add(TermTools.buildAnd(t1, t2));
                    }
                }
            } else {
                result.addAll(res1);
                result.addAll(res2);
            }

            return result;
        case NEQ:
        case LNOT:
            throw new UnsupportedException("The function symbol " + fSymb + " is not allowed in transformation to DNF");
        }

        result.add(t);

        return result;
    }


    public static TRSTerm getInteger(final TRSTerm t) {
        final TRSTerm valT = TermTools.evaluate(t);
        if (valT instanceof TRSFunctionApplication) {
            final FunctionSymbol fs = ((TRSFunctionApplication) valT).getRootSymbol();
            if (TermTools.PREDEFINED.isInt(fs, DomainFactory.INTEGERS)) {
                return valT;
                //return PREDEFINED.getInt(fs, DomainFactory.INTEGERS);
            }
        }
        return null;
    }

    public static TRSTerm evaluate(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return t;
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        if (fSymb.getArity() == 0) {
            return t;
        }

        final ArrayList<TRSTerm> vArgs = new ArrayList<>(fSymb.getArity());

        for (final TRSTerm arg : fApp.getArguments()) {
            vArgs.add(TermTools.evaluate(arg));
        }

        switch (f) {
        case CAST:
            return vArgs.get(0);

        case DIV:
        case MOD:
        case MUL: {
            final TRSTerm t1 = TermTools.getInteger(vArgs.get(0));

            if (t1 != null) {
                final BigInteger n1 =
                    TermTools.PREDEFINED.getInt(((TRSFunctionApplication) t1).getRootSymbol(), DomainFactory.INTEGERS);
                if (n1.equals(BigInteger.ZERO)) {
                    return vArgs.get(0);
                }

                final TRSTerm t2 = TermTools.getInteger(vArgs.get(1));

                if (t2 != null) {
                    final BigInteger n2 =
                        TermTools.PREDEFINED.getInt(((TRSFunctionApplication) t2).getRootSymbol(), DomainFactory.INTEGERS);

                    BigInteger val = null;

                    switch (f) {
                    case DIV:
                        val = n1.divide(n2);
                        break;
                    case MOD:
                        val = n1.mod(n2);
                        break;
                    case MUL:
                        val = n1.multiply(n2);
                        break;
                    }

                    return ToolBox.buildInt(val);
                }
            }

            if (f.equals(Function.DIV) && vArgs.get(0).equals(vArgs.get(1))) {
                return ToolBox.buildInt(BigInteger.ONE);
            }

            if (f.equals(Function.MOD) && (vArgs.get(0).equals(vArgs.get(1)) || BigInteger.ZERO.equals(TermTools.getInteger(vArgs.get(1))))) {
                return ToolBox.buildInt(BigInteger.ZERO);
            }

            if (f.equals(Function.MUL)
                && (BigInteger.ZERO.equals(TermTools.getInteger(vArgs.get(0))) || BigInteger.ZERO
                    .equals(TermTools.getInteger(vArgs.get(1)))))
            {
                return ToolBox.buildInt(BigInteger.ZERO);
            }
        }
        break;



        case GT:
        case GE:
        case EQ: {
            final TRSTerm a = vArgs.get(0);
            final TRSTerm b = vArgs.get(1);

            if (a.equals(b)) {
                if (f.equals(Function.GT)) {
                    return TermTools.FALSE;
                }
                if (f.equals(Function.EQ)) {
                    return TermTools.TRUE;
                }
            }

            final TRSTerm diff = ToolBox.buildSum(Arrays.asList(a, ToolBox.buildMinus(b)));

            try {
                final SimplePolynomial poly = TermTools.getSimplePolynomial(diff);

                ConstraintType type = null;

                switch (f) {
                case GT:
                    type = ConstraintType.GT;
                    break;
                case GE:
                    type = ConstraintType.GE;
                    break;
                case EQ:
                    type = ConstraintType.EQ;
                    break;
                }

                final SimplePolyConstraint c =  new SimplePolyConstraint(poly, type);

                if (poly.isConstant()) {
                    return c.isSatisfiable() ? TermTools.TRUE : TermTools.FALSE; // ToolBox.buildBool(c.isSatisfiable());
                }

            } catch (final UnsupportedException e) {

            }
        }
        break;

        case LE:
        case LT:
        case NEQ:

            final TRSTerm a = fApp.getArgument(0);
            final TRSTerm b = fApp.getArgument(1);

            if (a.equals(b)) {
                if (f.equals(Function.LT)) {
                    return TermTools.FALSE;
                }
                if (f.equals(Function.NEQ)) {
                    return TermTools.TRUE;
                }
            }

            TRSTerm revT = null;

            switch (f) {
            case LE:
                revT = ToolBox.buildGe(b, a);
                break;
            case LT:
                revT = ToolBox.buildGt(b, a);
                break;
            case NEQ:
                revT = TermTools.buildOr(ToolBox.buildGt(a, b), ToolBox.buildGt(b, a));
                break;
            }
            return TermTools.evaluate(revT);


        case LNOT:
            if (TermTools.isFalse(vArgs.get(0))) {
                return ToolBox.buildTrue();
            }

            if (TermTools.isTrue(vArgs.get(0))) {
                return ToolBox.buildFalse();
            }

            break;

        case LOR:

            return TermTools.buildOr(vArgs.get(0), vArgs.get(1));

        case LAND:
            return TermTools.buildAnd(vArgs.get(0), vArgs.get(1));
        }

        return TRSTerm.createFunctionApplication(fSymb, vArgs);
    }

    public static Set<FunctionSymbol> getUndefinedFSyms(final TRSTerm t) {
        final Set<FunctionSymbol> fSyms = new HashSet<>();

        for (final FunctionSymbol fs : t.getFunctionSymbols()) {
            if (!Function.isDefined(fs)) {
                fSyms.add(fs);
            }
        }

        return fSyms;
    }

    public static boolean isTrue(final TRSTerm t) {
        return (t instanceof TRSFunctionApplication)
            && TermTools.PREDEFINED.isBooleanTrue(((TRSFunctionApplication) t).getRootSymbol());
    }

    public static boolean isFalse(final TRSTerm t) {
        return (t instanceof TRSFunctionApplication)
            && TermTools.PREDEFINED.isBooleanFalse(((TRSFunctionApplication) t).getRootSymbol());
    }

    public static TRSTerm buildOr(final TRSTerm t1, final TRSTerm t2) {
        if (TermTools.isFalse(t1) || TermTools.isTrue(t2) || t2.equals(t1)) {
            return t2;
        }

        if (TermTools.isFalse(t2) || TermTools.isTrue(t1)) {
            return t1;
        }

        return ToolBox.buildOr(t1, t2);
    }

    public static TRSTerm buildAnd(final TRSTerm t1, final TRSTerm t2) {
        if (TermTools.isFalse(t1) || TermTools.isTrue(t2) || t2.equals(t1)) {
            return t1;
        }

        if (TermTools.isFalse(t2) || TermTools.isTrue(t1)) {
            return t2;
        }

        return ToolBox.buildAnd(t1, t2);
    }

    public static TRSTerm TRUE = ToolBox.buildTrue();
    public static TRSTerm FALSE = ToolBox.buildFalse();

    public static final IDPPredefinedMap PREDEFINED = IDPPredefinedMap.DEFAULT_MAP;

    public static enum Function {
        TRUE,
        FALSE,
        LNOT,
        LAND,
        LOR,
        BWNOT,
        BWAND,
        BWXOR,
        BWOR,
        CAST,
        ADD,
        SUB,
        MUL,
        DIV,
        MOD,
        UMINUS,
        GT,
        GE,
        EQ,
        NEQ,
        LE,
        LT;

        private static HashMap<FunctionSymbol, Function> fSymToFun = new HashMap<FunctionSymbol, Function>() {
            {
                this.put(TermTools.PREDEFINED.getBooleanTrue().getSym(), TRUE);
                this.put(TermTools.PREDEFINED.getBooleanFalse().getSym(), FALSE);
                this.put(TermTools.PREDEFINED.getSym(Func.Lnot, DomainFactory.BOOLEAN), LNOT);
                this.put(TermTools.PREDEFINED.getSym(Func.Land, DomainFactory.BOOLEAN), LAND);
                this.put(TermTools.PREDEFINED.getSym(Func.Lor, DomainFactory.BOOLEAN), LOR);
                this.put(TermTools.PREDEFINED.getSym(Func.Bwnot, DomainFactory.BOOLEAN), BWNOT);
                this.put(TermTools.PREDEFINED.getSym(Func.Bwand, DomainFactory.BOOLEAN), BWAND);
                this.put(TermTools.PREDEFINED.getSym(Func.Bwxor, DomainFactory.BOOLEAN), BWXOR);
                this.put(TermTools.PREDEFINED.getSym(Func.Bwor, DomainFactory.BOOLEAN), BWOR);
                this.put(TermTools.PREDEFINED.getSym(Func.Cast, DomainFactory.INTEGERS), CAST);
                this.put(TermTools.PREDEFINED.getSym(Func.Add, DomainFactory.INTEGERS), ADD);
                this.put(TermTools.PREDEFINED.getSym(Func.Sub, DomainFactory.INTEGERS), SUB);
                this.put(TermTools.PREDEFINED.getSym(Func.Mul, DomainFactory.INTEGERS), MUL);
                this.put(TermTools.PREDEFINED.getSym(Func.Div, DomainFactory.INTEGERS), DIV);
                this.put(TermTools.PREDEFINED.getSym(Func.Mod, DomainFactory.INTEGERS), MOD);
                this.put(TermTools.PREDEFINED.getSym(Func.UnaryMinus, DomainFactory.INTEGERS), UMINUS);
                this.put(TermTools.PREDEFINED.getSym(Func.Gt, DomainFactory.INTEGERS), GT);
                this.put(TermTools.PREDEFINED.getSym(Func.Ge, DomainFactory.INTEGERS), GE);
                this.put(TermTools.PREDEFINED.getSym(Func.Eq, DomainFactory.INTEGERS), EQ);
                this.put(TermTools.PREDEFINED.getSym(Func.Neq, DomainFactory.INTEGERS), NEQ);
                this.put(TermTools.PREDEFINED.getSym(Func.Le, DomainFactory.INTEGERS), LE);
                this.put(TermTools.PREDEFINED.getSym(Func.Lt, DomainFactory.INTEGERS), LT);
            }
        };

        private static List<FunctionSymbol> DEFINED_FSYMS = Arrays.asList(
            TermTools.PREDEFINED.getBooleanTrue().getSym(),
            TermTools.PREDEFINED.getBooleanFalse().getSym(),
            TermTools.PREDEFINED.getSym(Func.Lnot, DomainFactory.BOOLEAN),
            TermTools.PREDEFINED.getSym(Func.Land, DomainFactory.BOOLEAN),
            TermTools.PREDEFINED.getSym(Func.Lor, DomainFactory.BOOLEAN),
            TermTools.PREDEFINED.getSym(Func.Cast, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Add, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Sub, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Mod, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.UnaryMinus, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Gt, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Ge, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Eq, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Neq, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Le, DomainFactory.INTEGERS),
            TermTools.PREDEFINED.getSym(Func.Lt, DomainFactory.INTEGERS));

        public static BigInteger getBigInteger(final FunctionSymbol fs) {
            if (TermTools.PREDEFINED.isInt(fs, DomainFactory.INTEGERS)) {
                return PredefinedSemanticsFactory.getIntValue(fs, DomainFactory.INTEGERS);
            }

            return null;
        }

        public static boolean isInt(final FunctionSymbol fs) {
            return TermTools.PREDEFINED.isInt(fs, DomainFactory.INTEGERS);
        }

        public static boolean isDefined(final FunctionSymbol fs) {
            return Function.isInt(fs) || Function.DEFINED_FSYMS.contains(fs);
        }

        public static Function getFunction(final FunctionSymbol fs) {
            return Function.fSymToFun.get(fs);
        }
    }

    public static SimplePolynomial flattenSimplePolynomial(
        final TRSTerm t,
        final Map<FunctionSymbol, Set<String>> fSymToVars,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp,
        final FreshNameGenerator ng)
    {

        try {
            return TermTools.getSimplePolynomial(TermTools.flatten(t, fSymToVars, varsToFApp, ng));
        } catch (final UnsupportedException e) {
            return null;
        }
    }

    public static LinearConstraintsSystem flattenConstraintsSystem(
        final TRSTerm t,
        final Map<FunctionSymbol, Set<String>> fSymToVars,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp,
        final FreshNameGenerator ng)
    {

        try {
            return TermSATSolver.create(AbortionFactory.create()).getLinearConstraintsSystem(
                TermTools.flatten(t, fSymToVars, varsToFApp, ng));
        } catch (final UnsupportedException e) {
            return null;
        }
    }

    public static TRSTerm flatten(
        final TRSTerm t,
        final Map<FunctionSymbol, Set<String>> fSymToVars,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp,
        final FreshNameGenerator ng)
    {
        if (t == null) {
            return null;
        }

        if (t instanceof TRSVariable) {
            return t;
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fs = fApp.getRootSymbol();

        if (IDPPredefinedMap.DEFAULT_MAP.isLnot(fs) || IDPPredefinedMap.DEFAULT_MAP.isLor(fs)) {
            new RuntimeException("Function symbol not allowed in interpolation: " + fs);
        }

        final List<TRSTerm> args = fApp.getArguments();
        final ArrayList<TRSTerm> flatArgs = new ArrayList<>(args.size());

        for (final TRSTerm arg : args) {
            flatArgs.add(TermTools.flatten(arg, fSymToVars, varsToFApp, ng));
        }

        final TRSFunctionApplication flatFApp = TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(flatArgs));

        if (IDPPredefinedMap.DEFAULT_MAP.isAdd(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isBooleanFalse(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isBooleanTrue(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isEq(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isGt(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isGe(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isLand(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isLe(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isLt(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isInt(fs, DomainFactory.INTEGERS)
            || IDPPredefinedMap.DEFAULT_MAP.isSub(fs)
            || IDPPredefinedMap.DEFAULT_MAP.isUnaryMinus(fs))
        {
            return flatFApp;
        }

        if (IDPPredefinedMap.DEFAULT_MAP.isMul(fs)) {
            if (flatFApp.getArgument(0).getVariables().isEmpty() || flatFApp.getArgument(1).getVariables().isEmpty()) {
                return flatFApp;
            }
        }

        final TRSVariable freshVar = TRSTerm.createVariable(ng.getFreshName("v", false));

        if (!fSymToVars.containsKey(fs)) {
            fSymToVars.put(fs, new HashSet<String>());
        }

        fSymToVars.get(fs).add(freshVar.getName());

        final ArrayList<TRSVariable> varArgs = new ArrayList<>(flatArgs.size());
        final List<String> varArgsN = new ArrayList<>(flatArgs.size());

        for (final TRSTerm arg : flatArgs) {
            TRSVariable fVarArg;

            if (!(arg instanceof TRSVariable)) { // && !arg.getVariables().isEmpty()) {
                fVarArg = TRSTerm.createVariable(ng.getFreshName("v", false));

                final ArrayList<String> vars = new ArrayList<>();

                for (final TRSVariable v : fVarArg.getVariables()) {
                    vars.add(v.getName());
                }

                varsToFApp.put(fVarArg.getName(), new Pair<TRSFunctionApplication, List<String>>(
                    (TRSFunctionApplication) arg,
                    vars));
            } else {
                fVarArg = (TRSVariable) arg;
            }

            varArgs.add(fVarArg);
            varArgsN.add(fVarArg.getName());

        }

        final TRSFunctionApplication varFApp = TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(varArgs));
        varsToFApp.put(freshVar.getName(), new Pair<>(fApp, varArgsN));

        return freshVar;
    }

    public static SMTExpression<SBool> toSMTBoolExp(final TRSTerm t, final VariableScope scope) throws UnsupportedException {
        final UnsupportedException unSupEx =  new UnsupportedException("The term "
            + t.toString()
            + " can not be transfered to SMT boolean expression");

        if (t instanceof TRSVariable) {
            throw unSupEx;
        }

        final Set<TRSTerm> result = new HashSet<>();

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        switch (f) {
        case TRUE:
            return Core.True;
        case FALSE:
            return Core.False;
        case GT:
        case GE: {
            final SMTExpression<SInt> a = TermTools.toSMTIntExp(fApp.getArgument(0), scope);
            final SMTExpression<SInt> b = TermTools.toSMTIntExp(fApp.getArgument(1), scope);

            switch (f) {
            case GT:
                return Ints.greater(a,b);
            case GE:
                return Ints.greaterEqual(a,b);
            }
        }
        break;

        case EQ:
        case LE:
        case LT:
        case NEQ: {
            final TRSTerm a = fApp.getArgument(0);
            final TRSTerm b = fApp.getArgument(1);

            TRSTerm revT = null;

            switch (f) {
            case EQ:
                revT = TermTools.buildAnd(ToolBox.buildGe(a, b), ToolBox.buildGe(b, a));
                break;
            case LE:
                revT = ToolBox.buildGt(b, a);
                break;
            case LT:
                revT = ToolBox.buildGe(b, a);
                break;
            case NEQ:
                revT = TermTools.buildOr(ToolBox.buildGt(a, b), ToolBox.buildGt(b, a));
                break;
            }
            return TermTools.toSMTBoolExp(revT, scope);
        }

        case LNOT:
            return Core.not(TermTools.toSMTBoolExp(fApp.getArgument(0), scope));

        case LOR:
        case LAND: {
            final SMTExpression<SBool> a = TermTools.toSMTBoolExp(fApp.getArgument(0), scope);
            final SMTExpression<SBool> b = TermTools.toSMTBoolExp(fApp.getArgument(1), scope);
            switch (f) {
            case LAND:
                return Core.and(a,b);
            case LOR:
                return Core.or(a,b);
            }
        }

        default:
        }

        throw unSupEx;

    }

    private static SMTExpression<SInt> toSMTIntExp(final TRSTerm t, final VariableScope scope) throws UnsupportedException {
        final UnsupportedException unSupEx =
            new UnsupportedException("The term " + t.toString() + " can not be transfered to SMT int expression");

        if (t instanceof TRSVariable) {
            return scope.intVar(t.getName());
        }

        final Set<TRSTerm> result = new HashSet<>();

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final Function f = Function.getFunction(fSymb);

        if (TermTools.PREDEFINED.isInt(fSymb, DomainFactory.INTEGERS)) {
            return Ints.constant(TermTools.PREDEFINED.getInt(fSymb, DomainFactory.INTEGERS));
        }

        switch (f) {
        case ADD:
        case SUB:
        case DIV:
        case MOD:
        case MUL: {
            final SMTExpression<SInt> a = TermTools.toSMTIntExp(fApp.getArgument(0), scope);
            final SMTExpression<SInt> b = TermTools.toSMTIntExp(fApp.getArgument(1), scope);

            switch (f) {
            case ADD:
                return Ints.add(a, b);
            case SUB:
                return Ints.subtract(a, b);
            case DIV:
                return Ints.div(a, b);
            case MOD:
                return Ints.mod(a, b);
            case MUL:
                return Ints.times(a, b);
            }
        }
        case UMINUS:
            return Ints.negate(TermTools.toSMTIntExp(fApp.getArgument(0), scope));
        }

        throw unSupEx;
    }

}
