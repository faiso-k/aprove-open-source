package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Interpolation;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.Disjunctions.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;


/**
 * @author marinag
 * Finds linear interpolants of linear constraints systems and of sequences of linear constraint systems
 */
public final class InterpolationSolver {

    /**
     * Aborter
     */
    private final Abortion aborter;

    /**
     * Constraints disjunction solver
     */
    private final DisjunctionSolver disjSolver;

    /**
     * Constraints systems solver
     */
    private final ConstraintsSystemSolver consSysSolver;

    final Map<FunctionSymbol, Set<String>> fSymToVar;
    final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF;
    final FreshNameGenerator ng;

    /**
     * @param consSysSolver Constraints systems solver
     * @param disjSolver Constraints disjunction solver
     * @param aborter Aborter
     */
    private InterpolationSolver(
        final Map<FunctionSymbol, Set<String>> fSymToVar,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF,
        final FreshNameGenerator ng,
        final Abortion aborter)
    {
        this.aborter = aborter;
        this.consSysSolver = ConstraintsSystemSolver.create(aborter);
        this.disjSolver = DisjunctionSolver.create(this.consSysSolver, aborter);
        this.varToF = varToF;
        this.fSymToVar = fSymToVar;
        this.ng = ng;
    }

    /**
     * @param consSysSolver Constraints systems solver
     * @param disjSolver Constraints disjunction solver
     * @param aborter Aborter
     * @return an interpolation solver initialized with given parameters
     */
    public static InterpolationSolver create(
        final Map<FunctionSymbol, Set<String>> fSymToVar,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF,
        final FreshNameGenerator ng,
        final Abortion aborter)
    {
        return new InterpolationSolver(fSymToVar, varToF, ng, aborter);
    }

    /**
     * @param a - Linear constraints system
     * @param b - Linear constraints system
     * @return If could be found: an interpolation I of a and b, where a implies I and I implies ~b. Otherwise, returns null.
     */
    private SimplePolyConstraint tryInterpolate(final LinearConstraintsSystem a, final LinearConstraintsSystem b)
    {
        final List<SimplePolynomial> A = a.toGeConstraintsSystem().getPolynomials();
        final List<SimplePolynomial> B = b.toGeConstraintsSystem().getPolynomials();

        final List<SimplePolynomial> C = new ArrayList<>();
        C.addAll(A);
        B.removeAll(A);
        C.addAll(B);

        final Set<String> variables = new HashSet<>();
        variables.addAll(a.getVariables());
        variables.addAll(b.getVariables());

        final List<String> varList = new ArrayList<>(variables);


        final FormulaFactory<SMTLIBTheoryAtom> factory = new FullSharingFactory<SMTLIBTheoryAtom>();

        final Set<SimplePolynomial> aCoefs = new HashSet<>();
        final Set<SimplePolynomial> bCoefs = new HashSet<>();

        final BigInteger[][] M = new BigInteger[varList.size()][C.size()];
        final BigInteger[] numAdd = new BigInteger[C.size()];

        final Map<String, SimplePolynomial> columnToPoly = new HashMap<>();
        final Map<String, BigInteger> columnToAddend = new HashMap<>();

        final List<SimplePolyConstraint> constraints = new ArrayList<>();

        final Set<SimplePolynomial> addends = new HashSet<>();

        for (int j = 0; j < C.size(); j++) {
            final IndefinitePart indef = IndefinitePart.create("c" + j,1);
            constraints
            .add(new SimplePolyConstraint(SimplePolynomial.create(indef, BigInteger.ONE), ConstraintType.GE));


            if (!C.get(j).getNumericalAddend().equals(BigInteger.ZERO)) {
                addends.add(SimplePolynomial.create(indef,C.get(j).getNumericalAddend()));
            }

            if (j<A.size()) {
                columnToAddend.put("c" + j, C.get(j).getNumericalAddend());
                columnToPoly.put("c" + j, C.get(j));
                aCoefs.add(SimplePolynomial.create(indef,BigInteger.ONE));
            } else {
                bCoefs.add(SimplePolynomial.create(indef,BigInteger.ONE));
            }
        }

        final SimplePolynomial addendsSum = SimplePolynomial.plus(addends);

        for (int i = 0; i < varList.size(); i++) {
            final Map<IndefinitePart, BigInteger> monomials = new HashMap<>();
            final IndefinitePart indefC = IndefinitePart.create(varList.get(i), 1);

            for (int j = 0; j < C.size(); j++) {
                final IndefinitePart indef = IndefinitePart.create("c" + j,1);

                final ImmutableMap<IndefinitePart, BigInteger> monomialsC = C.get(j).getSimpleMonomials();

                if (monomialsC.containsKey(indefC)) {
                    final BigInteger coef = monomialsC.get(indefC);
                    monomials.put(indef, coef);
                }

            }
            constraints.add(new SimplePolyConstraint(SimplePolynomial.create(monomials), ConstraintType.EQ));
        }

        final List<Formula<SMTLIBTheoryAtom>> basic = new ArrayList<>();

        for (final SimplePolyConstraint constraint : constraints) {
            basic.add(factory.buildTheoryAtom(constraint.toSMTLIB()));
        }


        final List<Formula<SMTLIBTheoryAtom>> formulas1 = new ArrayList<>(basic);

        final SimplePolyConstraint addendsConstraint =
            new SimplePolyConstraint(addendsSum.negate().minus(SimplePolynomial.ONE), ConstraintType.GE);
        formulas1.add(factory.buildTheoryAtom(addendsConstraint.toSMTLIB()));

        final ConstraintType type = ConstraintType.GE;

        try {

            final Pair<YNM, Map<String, String>> answer = ToolBox.SMT_ENGINE.solve(formulas1, SMTLogic.QF_LIA, this.aborter);

            //                        if (!answer.x.equals(YNM.YES) || answer.y.isEmpty()) {
            //                            type = ConstraintType.GT;
            //
            //                            final List<Formula<SMTLIBTheoryAtom>> formulas2 = new ArrayList<>(basic);
            //
            //                            addendsConstraint = new SimplePolyConstraint(addendsSum, ConstraintType.GE);
            //                            formulas2.add(factory.buildTheoryAtom(addendsConstraint.toSMTLIB()));
            //
            //                            SimplePolyConstraint coefsConstraint =
            //                                new SimplePolyConstraint(SimplePolynomial.plus(aCoefs), ConstraintType.GT);
            //                            formulas2.add(factory.buildTheoryAtom(coefsConstraint.toSMTLIB()));
            //
            //                            answer = ToolBox.SMT_ENGINE.solve(formulas2, SMTLogic.QF_LIA, this.aborter);
            //
            //                            if (!answer.x.equals(YNM.YES) || answer.y.isEmpty()) {
            //                                type = ConstraintType.GE;
            //
            //                                final List<Formula<SMTLIBTheoryAtom>> formulas3 = new ArrayList<>(basic);
            //
            //                                formulas3.add(factory.buildTheoryAtom(addendsConstraint.toSMTLIB()));
            //
            //                                coefsConstraint = new SimplePolyConstraint(SimplePolynomial.plus(bCoefs), ConstraintType.GT);
            //                                formulas3.add(factory.buildTheoryAtom(coefsConstraint.toSMTLIB()));
            //
            //                                answer = ToolBox.SMT_ENGINE.solve(formulas3, SMTLogic.QF_LIA, this.aborter);
            //                            }
            //                        }

            if (!answer.x.equals(YNM.YES) || answer.y.isEmpty()) {
                return null;
            }

            final Set<SimplePolynomial> resultPolys = new HashSet<>();
            for (final Entry<String, String> entry : answer.y.entrySet()) {
                if (!columnToPoly.containsKey(entry.getKey())) {
                    continue;
                }

                final BigInteger coef = new BigInteger(entry.getValue());

                if (coef.equals(BigInteger.ZERO)) {
                    continue;
                }

                resultPolys.add(columnToPoly.get(entry.getKey()).times(coef));
            }

            final SimplePolynomial resultSum = SimplePolynomial.plus(resultPolys);

            if (resultSum.isZero()) {
                return null;
            }

            final SimplePolyConstraint result = new SimplePolyConstraint(resultSum, type);

            return result;

        } catch (final AbortionException e) {
            throw e;
        } catch (final WrongLogicException e) {
            return null;
        }

    }

    /**
     * @param a - Linear constraints system
     * @param b - Linear constraints system
     * @return If could be found: an interpolation I of a and b, where a implies I and I implies ~b. Otherwise, returns null.
     */
    public SimplePolyConstraint solve(final LinearConstraintsSystem a, final LinearConstraintsSystem b) {
        if (b.isTrue()) {
            return null;
        }

        final Pair<LinearConstraintsSystem, LinearConstraintsSystem> pair = new Pair<>(a, b);

        synchronized (this.SOLUTION_SimplePolyConstraint) {
            if (this.SOLUTION_SimplePolyConstraint.containsKey(pair)) {
                // already done
                return this.SOLUTION_SimplePolyConstraint.get(pair);
            }

            for (final Pair<LinearConstraintsSystem, LinearConstraintsSystem> p : this.SOLUTION_SimplePolyConstraint
                .keySet())
            {
                if (this.SOLUTION_SimplePolyConstraint.get(p) != null) {
                    if (a.contains(p.x) && b.contains(p.y)) {
                        // a implies p.x
                        // p.x implies I and I implies ~p.y
                        // b implies p.y => ~p.y implies ~b
                        // => a implies I and I implies ~b

                        return this.SOLUTION_SimplePolyConstraint.get(p);
                    }
                } else if (p.x.contains(a) && p.y.contains(b)) {
                    // p.x implies a
                    // p.x does not imply ~p.y
                    // p.y implies b => ~b implies ~p.y
                    // => a does not imply ~b

                    return null;
                }
            }
        }

        //                final LinearConstraintsSystem c = LinearConstraintsSystem.merge(a, b);
        //
        //                LinearConstraintsSystem constraints = c.transpose(null, ConstraintType.EQ, null, null);
        //                constraints =
        //                    LinearConstraintsSystem.create(constraints.addAllConstraints(constraints
        //                        .getAllVariablesNonNegativeConstraints()));
        //                constraints =
        //                    LinearConstraintsSystem.create(constraints.addConstraint(new SimplePolyConstraint(c
        //                        .transposeAddend()
        //                        .times(BigInteger.ONE.negate())
        //                        .minus(SimplePolynomial.create(BigInteger.ONE)), ConstraintType.GE)));
        //
        //                final ImmutableMap<IndefinitePart, BigInteger> result = this.consSysSolver.solve(constraints);
        //
        //                if (result == null) {
        //                    this.SOLUTION_SimplePolyConstraint.put(pair, null);
        //                    return null;
        //                }
        //
        //                final ArrayList<SimplePolynomial> polyList = new ArrayList<>();
        //
        //                for (int j = 0; j < c.size(); j++) {
        //                    final BigInteger n = result.get(IndefinitePart.create(constraintIdentifier(j), 1));
        //
        //                    if (n != null && !n.equals(BigInteger.ZERO)) {
        //                        final SimplePolyConstraint constraint = c.get(j);
        //                        if (a.contains(constraint)) {
        //                            polyList.add(constraint.getPolynomial().times(n));
        //                        }
        //                    }
        //                }

        // try interpolate the pair
        final SimplePolyConstraint solution = this.tryInterpolate(a, b);

        // save results for future generations
        synchronized (this.SOLUTION_SimplePolyConstraint) {
            this.SOLUTION_SimplePolyConstraint.put(pair, solution);
        }
        return solution;
    }

    /**
     * Interpolation
     *
     * @param a - Disjunction of constraints systems
     * @param b - Disjunction of constraints systems
     * @return Interpolation of a and b
     */
    public PolyDisjunction solve(final PolyDisjunction a, final PolyDisjunction b)
    {
        final Pair<PolyDisjunction, PolyDisjunction> pair = new Pair<>(a, b);

        synchronized (this.SOLUTION_DisjunctionGeneralConstraintsSystem) {
            if (this.SOLUTION_DisjunctionGeneralConstraintsSystem.containsKey(pair)) {
                return this.SOLUTION_DisjunctionGeneralConstraintsSystem.get(pair);
            }
        }

        PolyDisjunction result = PolyDisjunction.FALSE;

        for (final PolyConstraintsSystem systemA : a.getConstraintsSystems()) {
            PolyConstraintsSystem interpolant = PolyConstraintsSystem.TRUE;
            for (final PolyConstraintsSystem systemB : b.getConstraintsSystems()) {
                final PolyConstraintsSystem item = this.solve(systemA, systemB);
                if (item != null) {
                    interpolant = interpolant.merge(item);
                }
            }
            if (!interpolant.isEmpty()) {
                result = result.addSystem(interpolant);
            }
        }

        this.SOLUTION_DisjunctionGeneralConstraintsSystem.put(pair, (PolyDisjunction) result.clone());
        return result;
    }

    /**
     * Interpolation
     *
     * @param a - Disjunction of linear constraints systems
     * @param b - Disjunction of linear constraints systems
     * @return Interpolation of a and b
     */
    private LinearDisjunction solveLinear(final LinearDisjunction a, final LinearDisjunction b)
    {
        final Pair<LinearDisjunction, LinearDisjunction> pair = new Pair<>(a, b);

        synchronized (this.SOLUTION_DisjunctionLinearConstraintsSystem) {
            if (this.SOLUTION_DisjunctionLinearConstraintsSystem.containsKey(pair)) {
                return this.SOLUTION_DisjunctionLinearConstraintsSystem.get(pair);
            }
        }

        final Collection<PolyConstraintsSystem> constraints = new HashSet<>();

        for (final LinearConstraintsSystem systemA : a.getLinearConstraintsSystems()) {
            PolyConstraintsSystem interpolant = PolyConstraintsSystem.TRUE;
            for (final LinearConstraintsSystem systemB : b.getLinearConstraintsSystems()) {

                final SimplePolyConstraint item = this.solve(systemA, systemB);
                if (item != null) {
                    interpolant = interpolant.addConstraint(item);
                }
            }
            if (!interpolant.isEmpty()) {
                constraints.add(interpolant);
            }
        }

        final LinearDisjunction result = LinearDisjunction.create(constraints);

        synchronized (this.SOLUTION_DisjunctionLinearConstraintsSystem) {
            this.SOLUTION_DisjunctionLinearConstraintsSystem.put(pair, result);
        }

        return result;
    }

    /**
     * Reverse map
     * @param originalIndefinite - map of indefinite parts to string
     * @return - reversed map
     */
    public static HashMap<String, IndefinitePart> reverse(final HashMap<IndefinitePart, String> originalIndefinite) {
        final HashMap<String, IndefinitePart> result = new HashMap<>();
        for (final IndefinitePart indef : originalIndefinite.keySet()) {
            result.put(originalIndefinite.get(indef), indef);
        }
        return result;
    }

    /**
     * Interpolation
     *
     * @param a - Constraints system
     * @param b - Constraints system
     * @return Interpolation of a and b
     */
    public PolyConstraintsSystem solve(final PolyConstraintsSystem a, final PolyConstraintsSystem b) {
        PolyConstraintsSystem result = PolyConstraintsSystem.TRUE;
        final PolyConstraintsSystem c = PolyConstraintsSystem.merge(a, b);
        if (a.getConstraints().containsAll(b.getConstraints()) || this.consSysSolver.isSAT(c)) {
            return null;
        }

        if (a.isLinear() && b.isLinear()) {
            final SimplePolyConstraint constraint =
                this.solve(a.getLinearPart(), b.getLinearPart());

            if (constraint != null && constraint.isSatisfiable()) {
                return PolyConstraintsSystem.create(constraint);
            }

            return null;
        }

        final Pair<PolyConstraintsSystem, PolyConstraintsSystem> pair = new Pair<>(a, b);

        if (this.SOLUTION_GeneralConstraintsSystem.containsKey(pair)) {
            // already done
            return this.SOLUTION_GeneralConstraintsSystem.get(pair);
        }

        // linearize the systems, treat multiplication as an undefined function

        final HashMap<SimplePolynomial, String> freshVars = new HashMap<>();
        final HashMap<String, ArrayList<String>> functions = new HashMap<>();
        final HashMap<IndefinitePart, String> originalIndefinite = new HashMap<>();

        this.consSysSolver.flatten(a, freshVars, functions, originalIndefinite);
        this.consSysSolver.flatten(b, freshVars, functions, originalIndefinite);

        final LinearConstraintsSystem linA = this.consSysSolver.toLinearConstraintsSystem(a, originalIndefinite);
        final LinearConstraintsSystem linB = this.consSysSolver.toLinearConstraintsSystem(b, originalIndefinite);

        final HashSet<Pair<String, String>> functionPairs = new HashSet<>();

        for (final String f1 : functions.keySet()) {
            for (final String f2 : functions.keySet()) {
                if (f2.equals(f1)
                    || functions.get(f1).size() != functions.get(f2).size()
                    || functionPairs.contains(new Pair<>(f2, f1)))
                {
                    continue;
                }
                functionPairs.add(new Pair<>(f1, f2));
            }
        }

        final LinearDisjunction resLin = this.solve(linA, linB, freshVars, functions, functionPairs);

        if (resLin.isEmpty()) {
            result = null;
        } else {
            // one of the found interpolants is enough
            final LinearConstraintsSystem linConstraints = resLin.getLinearConstraintsSystems().iterator().next();

            result = PolyConstraintsSystem.merge(result, linConstraints.replaceIndefinite(InterpolationSolver.reverse(originalIndefinite)));

            if (result.isEmpty()) {
                result = null;
            }
        }

        synchronized (this.SOLUTION_GeneralConstraintsSystem) {
            this.SOLUTION_GeneralConstraintsSystem.put(pair, result);
        }

        return result == null ? null : result;
    }

    /**
     * Check if id is local in positive and not in negative
     * @param id - variable name
     * @param positive - positive linear constraints system
     * @param negative - negative linear constraints system
     * @param functions - functions map
     * @return true - if is local only in positive, false - otherwise
     */
    private boolean isLocal(
        final String id,
        final LinearConstraintsSystem positive,
        final LinearConstraintsSystem negative,
        final HashMap<String, ArrayList<String>> functions)
    {
        if (positive.getVariables().contains(id)) {
            boolean result = true;

            for (final String var : functions.get(id)) {
                for (final Entry<String, ArrayList<String>> entry : functions.entrySet()) {
                    result =
                        result
                        && (!negative.getVariables().contains(entry.getKey()) || !entry.getValue().contains(var));
                }
            }

            return result;
        }

        return false;
    }

    private TRSTerm flatten(
        final TRSTerm t,
        final Map<FunctionSymbol, Set<TRSVariable>> fSymToVars,
        final Map<TRSVariable, TRSFunctionApplication> varsToFApp,
        final FreshNameGenerator ng)
    {
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
            flatArgs.add(this.flatten(arg, fSymToVars, varsToFApp, ng));
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
            fSymToVars.put(fs, new HashSet<TRSVariable>());
        }

        fSymToVars.get(fs).add(freshVar);


        final ArrayList<TRSVariable> varArgs = new ArrayList<>(flatArgs.size());

        for (final TRSTerm arg : flatArgs) {
            TRSVariable fVarArg;

            if (!(arg instanceof TRSVariable)) {
                fVarArg = TRSTerm.createVariable(ng.getFreshName("v", false));
                varsToFApp.put(fVarArg, (TRSFunctionApplication) arg);
            } else {
                fVarArg = (TRSVariable) arg;
            }

            varArgs.add(fVarArg);
        }

        final TRSFunctionApplication varFApp = TRSTerm.createFunctionApplication(fs, ImmutableCreator.create(varArgs));
        varsToFApp.put(freshVar, varFApp);

        return freshVar;
    }

    /**
     * @param f
     * @param negVars
     * @param varToF
     * @return
     */
    private boolean isLocal(
        final String f,
        final Set<String> negVars,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF)
    {
        if (varToF.containsKey(f)) {
            for (final TRSTerm arg : varToF.get(f).x.getArguments()) {
                if (!this.isLocal(((TRSVariable) arg).getName(), negVars, varToF)) {
                    return false;
                }
            }
            return true;
        } else {
            for (final String v : negVars) {
                if (varToF.containsKey(v)) {
                    if (varToF.get(v).y.contains(f)) {
                        return false;
                    }
                }
            }

            return true;
        }
    }

    /**
     * Interpolation
     *
     * @param A - Linear constraints system
     * @param B - Linear constraints system
     * @param freshVars - Fresh variables map
     * @param functions - Functions map
     * @param originalFunctionPairs - Functions pairs
     * @return Interpolations of originalA and origianlB
     */
    public LinearDisjunction solve(
        final LinearConstraintsSystem A,
        final LinearConstraintsSystem B,
        final Set<Pair<String, String>> fPairs,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF,
        final FreshNameGenerator ng)
    {
        LinearConstraintsSystem a = LinearConstraintsSystem.create(A);
        LinearConstraintsSystem b = LinearConstraintsSystem.create(B);

        final HashSet<String> funcs = new HashSet<>();

        final HashSet<String> localsA = new HashSet<>();
        final HashSet<String> localsB = new HashSet<>();

        for (final String f : varToF.keySet()) {
            if (a.getVariables().contains(f) && this.isLocal(f, b.getVariables(), varToF)) {
                localsA.add(f);
                funcs.add(f);
            } else if (b.getVariables().contains(f) && this.isLocal(f, a.getVariables(), varToF)) {
                localsB.add(f);
                funcs.add(f);
            }
        }

        final Set<Pair<String, String>> functionPairs = new HashSet<>();

        for (final Pair<String, String> p : fPairs) {
            if (funcs.contains(p.x) && funcs.contains(p.y)) {
                functionPairs.add(p);
            }
        }

        final LinearConstraintsSystem c = LinearConstraintsSystem.create(PolyConstraintsSystem.merge(a, b));

        if (!functionPairs.isEmpty()) {
            final Pair<String, String> functionPair = functionPairs.iterator().next();

            final String f1 = functionPair.x;
            final String f2 = functionPair.y;

            final ArrayList<SimplePolynomial> ci = new ArrayList<>();
            final ArrayList<SimplePolynomial> di = new ArrayList<>();

            for (final String v : varToF.get(f1).y) {
                ci.add(SimplePolynomial.create(v));
            }

            for (final String v : varToF.get(f2).y) {
                di.add(SimplePolynomial.create(v));
            }

            final ArrayList<SimplePolynomial> polys = new ArrayList<>();

            for (int i = 0; i < ci.size(); i++) {
                polys.add(ci.get(i).minus(di.get(i)));
                polys.add(di.get(i).minus(ci.get(i)));
            }

            PolyDisjunction parNeq = PolyDisjunction.FALSE;
            LinearDisjunction parNeqLin = LinearDisjunction.create(PolyDisjunction.FALSE);

            LinearDisjunction parEqLin = LinearDisjunction.create(PolyDisjunction.FALSE);

            LinearConstraintsSystem parEqCon = LinearConstraintsSystem.create();

            for (final SimplePolynomial p : polys) {
                if (!p.isZero()) {
                    parNeq =
                        parNeq
                        .addSystem(LinearConstraintsSystem.create(new SimplePolyConstraint(p, ConstraintType.GT)));
                    parNeqLin =
                        parNeqLin.addSystem(LinearConstraintsSystem.create(new SimplePolyConstraint(
                            p,
                            ConstraintType.GT)));
                    parEqCon = parEqCon.addConstraint(new SimplePolyConstraint(p, ConstraintType.GE));
                }
            }

            parEqLin = parEqLin.addSystem(parEqCon);

            LinearDisjunction i1;
            LinearDisjunction i0;

            if (this.isImplied(c, parEqCon))
            {
                if (localsA.contains(f1) && !localsA.contains(f2) && localsB.contains(f2) && !localsB.contains(f1)) {
                    i1 = LinearDisjunction.FALSE;
                    i0 = LinearDisjunction.FALSE;

                    final int argSize = varToF.get(f1).y.size();

                    final FunctionSymbol fs = varToF.get(f1).x.getRootSymbol();

                    final ArrayList<Pair<SimplePolynomial, SimplePolynomial>> t = new ArrayList<>(argSize);

                    for (int i = 0; i < argSize; i++) {
                        final String arg1 = varToF.get(f1).y.get(i);
                        final String arg2 = varToF.get(f2).y.get(i);

                        if (arg1.equals(arg2)) {
                            continue;
                        }

                        final Pair<SimplePolynomial, SimplePolynomial> pair =
                            this.separate(a, b, arg1, arg2);

                        if (pair != null) {
                            t.add(pair);
                        }
                    }

                    final ArrayList<SimplePolynomial> p = new ArrayList<>();

                    for (final Pair<SimplePolynomial, SimplePolynomial> pl : t) {
                        p.add(pl.x.minus(pl.y));
                    }

                    for (final SimplePolynomial pl : p) {
                        final LinearConstraintsSystem sys =
                            LinearConstraintsSystem.create(new SimplePolyConstraint(pl, ConstraintType.GT));

                        if (this.consSysSolver.isSAT(sys)) {
                            i0 = i0.addSystem(sys);
                        }
                    }

                    LinearConstraintsSystem E = LinearConstraintsSystem.create();

                    for (final SimplePolynomial pl : p) {
                        E = E.addConstraint(new SimplePolyConstraint(pl, ConstraintType.GE));
                    }
                    i1 = i1.addSystem(E);

                    final TRSVariable freshVar = TRSTerm.createVariable(ng.getFreshName("v", false));

                    final ArrayList<TRSTerm> argsT = new ArrayList<>(argSize);
                    for (final Pair<SimplePolynomial, SimplePolynomial>  pl : t) {
                        argsT.add(pl.x.toTerm());
                    }

                    final TRSFunctionApplication fApp = TRSTerm.createFunctionApplication(fs, argsT);


                    varToF.put(freshVar.getName(), new Pair<TRSFunctionApplication, List<String>>(fApp, null));
                    a =
                        a.addConstraint(new SimplePolyConstraint(SimplePolynomial.create(f1).minus(
                            SimplePolynomial.create(freshVar.getName())), ConstraintType.EQ));
                    b =
                        b.addConstraint(new SimplePolyConstraint(SimplePolynomial.create(f2).minus(
                            SimplePolynomial.create(freshVar.getName())), ConstraintType.EQ));


                } else if (localsA.contains(f1)
                    && localsA.contains(f2)
                    && !localsB.contains(f2)
                    && !localsB.contains(f1))
                {
                    LinearDisjunction aNew = LinearDisjunction.FALSE;
                    aNew = aNew.addSystem(a);
                    aNew = LinearDisjunction.create(aNew.mergeAll(LinearDisjunction.create(parNeqLin)));

                    final LinearDisjunction bNew = LinearDisjunction.create(b);

                    i1 = LinearDisjunction.TRUE;
                    i0 = this.solveLinear(aNew, bNew);

                    a =
                        a.addConstraint(new SimplePolyConstraint(SimplePolynomial.create(f1).minus(
                            SimplePolynomial.create(f2)), ConstraintType.EQ));

                } else {
                    final LinearDisjunction aNew = LinearDisjunction.create(a);

                    LinearDisjunction bNew = LinearDisjunction.FALSE;
                    bNew = bNew.addSystem(b);
                    bNew = LinearDisjunction.create(bNew.mergeAll(LinearDisjunction.create(parNeqLin)));

                    i1 = this.solveLinear(aNew, bNew);
                    i0 = LinearDisjunction.FALSE;

                    b =
                        b.addConstraint(new SimplePolyConstraint(SimplePolynomial.create(f1).minus(
                            SimplePolynomial.create(f2)), ConstraintType.EQ));
                }

                functionPairs.remove(functionPair);

                PolyDisjunction result = LinearDisjunction.create(i1.mergeAll(this.solve(a, b, functionPairs, varToF, ng)));

                result = result.addAllSystems(i0.getConstraintsSystems());

                return LinearDisjunction.create(result);
            }
        }

        final SimplePolyConstraint i = this.solve(a, b);
        PolyDisjunction result = PolyDisjunction.TRUE;

        if (i != null) {
            result = PolyDisjunction.create(i);
        }

        return LinearDisjunction.create(result);
    }

    private TRSTerm buildAnd(final TRSTerm a, final TRSTerm b) {
        if (Arrays.asList(a,b).contains(InterpolationSolver.BOOLEAN_FALSE)) {
            return InterpolationSolver.BOOLEAN_FALSE;
        }

        if (InterpolationSolver.BOOLEAN_FALSE.equals(a)) {
            return InterpolationSolver.BOOLEAN_TRUE;
        }
        if (InterpolationSolver.BOOLEAN_FALSE.equals(b)) {
            return InterpolationSolver.BOOLEAN_TRUE;
        }

        return ToolBox.buildAnd(a, b);
    }

    private TRSTerm buildOr (final TRSTerm a, final TRSTerm b)  {
        if (Arrays.asList(a,b).contains(InterpolationSolver.BOOLEAN_TRUE)) {
            return InterpolationSolver.BOOLEAN_TRUE;
        }

        if (InterpolationSolver.BOOLEAN_FALSE.equals(a)) {
            return b;
        }
        if (InterpolationSolver.BOOLEAN_FALSE.equals(b)) {
            return a;
        }

        return ToolBox.buildOr(a, b);
    }

    private static TRSTerm BOOLEAN_FALSE  = IDPPredefinedMap.DEFAULT_MAP.getBooleanFalse().getTerm();
    private static TRSTerm BOOLEAN_TRUE = IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getTerm();

    /**
     * Interpolation
     *
     * @param A - Linear constraints system
     * @param B - Linear constraints system
     * @param freshVars - Fresh variables map
     * @param functions - Functions map
     * @param originalFunctionPairs - Functions pairs
     * @return Interpolations of originalA and origianlB
     */
    public LinearDisjunction solve(
        final LinearConstraintsSystem A,
        final LinearConstraintsSystem B,
        final HashMap<SimplePolynomial, String> freshVars,
        final HashMap<String, ArrayList<String>> functions,
        final HashSet<Pair<String, String>> originalFunctionPairs)
    {
        LinearConstraintsSystem a = LinearConstraintsSystem.create(A);
        LinearConstraintsSystem b = LinearConstraintsSystem.create(B);

        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        ng.lockNames(a.getVariables());
        ng.lockNames(b.getVariables());

        final HashSet<String> funcs = new HashSet<>();

        final HashSet<String> localsA = new HashSet<>();
        final HashSet<String> localsB = new HashSet<>();

        for (final String f : functions.keySet()) {
            if (this.isLocal(f, a, b, functions)) {
                localsA.add(f);
                funcs.add(f);
            } else if (this.isLocal(f, b, a, functions)) {
                localsB.add(f);
                funcs.add(f);
            }
        }

        final HashSet<Pair<String, String>> functionPairs = new HashSet<>();

        for (final Pair<String, String> p : originalFunctionPairs) {
            if (funcs.contains(p.x) && funcs.contains(p.y)) {
                functionPairs.add(p);
            }
        }

        final LinearConstraintsSystem c = LinearConstraintsSystem.create(PolyConstraintsSystem.merge(a, b));



        if (!functionPairs.isEmpty()) {
            final Pair<String, String> functionPair = functionPairs.iterator().next();

            final String f1 = functionPair.x;
            final String f2 = functionPair.y;

            final ArrayList<SimplePolynomial> ci = new ArrayList<>();
            final ArrayList<SimplePolynomial> di = new ArrayList<>();

            for (final String v : functions.get(f1)) {
                ci.add(SimplePolynomial.create(v));
            }

            for (final String v : functions.get(f2)) {
                di.add(SimplePolynomial.create(v));
            }

            final ArrayList<SimplePolynomial> polys = new ArrayList<>();

            for (int i = 0; i < ci.size(); i++) {
                polys.add(ci.get(i).minus(di.get(i)));
                polys.add(di.get(i).minus(ci.get(i)));
            }

            PolyDisjunction parNeq = PolyDisjunction.FALSE;
            LinearDisjunction parNeqLin = LinearDisjunction.create(PolyDisjunction.FALSE);

            LinearDisjunction parEqLin = LinearDisjunction.create(PolyDisjunction.FALSE);

            LinearConstraintsSystem parEqCon = LinearConstraintsSystem.create();

            for (final SimplePolynomial p : polys) {
                if (!p.isZero()) {
                    parNeq =
                        parNeq
                        .addSystem(LinearConstraintsSystem.create(new SimplePolyConstraint(p, ConstraintType.GT)));
                    parNeqLin =
                        parNeqLin.addSystem(LinearConstraintsSystem
                            .create(new SimplePolyConstraint(p, ConstraintType.GT)));
                    parEqCon = parEqCon.addConstraint(new SimplePolyConstraint(p, ConstraintType.GE));
                }
            }

            parEqLin = parEqLin.addSystem(parEqCon);

            LinearDisjunction i1;
            LinearDisjunction i0;

            if (this.isImplied(c, parEqCon))
            {
                if (localsA.contains(f1) && !localsA.contains(f2) && localsB.contains(f2) && !localsB.contains(f1)) {
                    i1 = LinearDisjunction.FALSE;
                    i0 = LinearDisjunction.FALSE;

                    final ArrayList<Pair<SimplePolynomial, SimplePolynomial>> t = new ArrayList<>();

                    for (int i = 0; i < functions.get(f1).size(); i++) {
                        if (functions.get(f1).get(i).equals(functions.get(f2).get(i))) {
                            continue;
                        }

                        final Pair<SimplePolynomial, SimplePolynomial> pair =
                            this.separate(
                                a,
                                b,
                                functions.get(f1).get(i), functions.get(f2).get(i));

                        if (pair != null) {
                            t.add(pair);
                        }
                    }

                    final ArrayList<SimplePolynomial> p = new ArrayList<>();

                    for (final Pair<SimplePolynomial, SimplePolynomial> pl : t) {
                        p.add(pl.x.minus(pl.y));
                    }

                    for (final SimplePolynomial pl : p) {
                        final LinearConstraintsSystem sys =
                            LinearConstraintsSystem.create(new SimplePolyConstraint(pl, ConstraintType.GT));

                        if (this.consSysSolver.isSAT(sys)) {
                            i0 = i0.addSystem(sys);
                        }
                    }

                    LinearConstraintsSystem E = LinearConstraintsSystem.create();

                    for (final SimplePolynomial pl : p) {
                        E = E.addConstraint(new SimplePolyConstraint(pl, ConstraintType.GE));
                    }
                    i1 = i1.addSystem(E);

                    if (t.size() == 2) {
                        final String fresh = ng.getFreshName("v", false);

                        SimplePolynomial newFunc = null;
                        newFunc = t.get(0).x.times(t.get(1).x);

                        freshVars.put(newFunc, fresh);
                        a =
                            a.addConstraint(new SimplePolyConstraint(SimplePolynomial
                                .create(f1)
                                .minus(SimplePolynomial.create(fresh)), ConstraintType.EQ));
                        b =
                            b.addConstraint(new SimplePolyConstraint(SimplePolynomial
                                .create(f2)
                                .minus(SimplePolynomial.create(fresh)), ConstraintType.EQ));
                    }
                } else if (localsA.contains(f1)
                    && localsA.contains(f2)
                    && !localsB.contains(f2)
                    && !localsB.contains(f1))
                {
                    LinearDisjunction aNew = LinearDisjunction.FALSE;
                    aNew = aNew.addSystem(a);
                    aNew = LinearDisjunction.create(aNew.mergeAll(LinearDisjunction.create(parNeqLin)));

                    final LinearDisjunction bNew = LinearDisjunction.create(b);

                    i1 = LinearDisjunction.TRUE;
                    i0 = this.solveLinear(aNew, bNew);

                    a =
                        a.addConstraint(new SimplePolyConstraint(
                            SimplePolynomial.create(f1).minus(
                                SimplePolynomial.create(f2)), ConstraintType.EQ));

                } else {
                    final LinearDisjunction aNew = LinearDisjunction.create(a);


                    LinearDisjunction bNew = LinearDisjunction.FALSE;
                    bNew = bNew.addSystem(b);
                    bNew = LinearDisjunction.create(bNew.mergeAll(LinearDisjunction.create(parNeqLin)));

                    i1 = this.solveLinear(aNew, bNew);
                    i0 = LinearDisjunction.FALSE;

                    b =
                        b.addConstraint(new SimplePolyConstraint(
                            SimplePolynomial.create(f1).minus(
                                SimplePolynomial.create(f2)), ConstraintType.EQ));
                }

                @SuppressWarnings("unchecked")
                final HashSet<Pair<String, String>> newFunctionPairs =
                (HashSet<Pair<String, String>>) functionPairs.clone();
                newFunctionPairs.remove(functionPair);

                LinearDisjunction result =
                    LinearDisjunction.create(i1.mergeAll(this.solve(a, b, freshVars, functions, newFunctionPairs)));

                result = LinearDisjunction.merge(result, i0);

                return result;
            }
        }

        final SimplePolyConstraint i = this.solve(a, b);
        LinearDisjunction result = LinearDisjunction.FALSE;

        if (i != null) {
            result = result.addSystem(LinearConstraintsSystem.create(i));
        }

        return result;
    }


    /**
     * Separate with local variables
     * @param a - linear constraints system
     * @param b - linear constraints system
     * @param x - local in a
     * @param y - local in b
     * @return pair of polynomials, lower and upper bounds
     */
    private Pair<SimplePolynomial, SimplePolynomial> separate(
        final LinearConstraintsSystem a,
        final LinearConstraintsSystem b,
        final String x,
        final String y)
        {
        if (b.getVariables().contains(x) || a.getVariables().contains(y))
        {
            throw new RuntimeException("Invalid parameters for separation");
        }

        final LinearConstraintsSystem c = LinearConstraintsSystem.merge(a, b);

        final HashMap<IndefinitePart, BigInteger> numericalAddend = new HashMap<>();
        numericalAddend.put(IndefinitePart.create(x, 1), BigInteger.ONE);
        numericalAddend.put(IndefinitePart.create(y, 1), BigInteger.ONE.negate());

        LinearConstraintsSystem plusConstraints = this.transpose(c, numericalAddend, ConstraintType.EQ, null, null);
        plusConstraints = plusConstraints.merge(this.getAllVariablesNonNegativeConstraints(plusConstraints));
        plusConstraints =
            plusConstraints.addConstraint(new SimplePolyConstraint(this.transposeAddend(c), ConstraintType.GE));

        numericalAddend.put(IndefinitePart.create(x, 1), BigInteger.ONE.negate());
        numericalAddend.put(IndefinitePart.create(y, 1), BigInteger.ONE);

        LinearConstraintsSystem minusConstraints = this.transpose(c, numericalAddend, ConstraintType.EQ, null, null);
        minusConstraints = minusConstraints.merge(this.getAllVariablesNonNegativeConstraints(minusConstraints));
        minusConstraints =
            minusConstraints.addConstraint(new SimplePolyConstraint(this.transposeAddend(c), ConstraintType.GE));

        final ImmutableMap<String, BigInteger> solutionPlus =
            this.consSysSolver.solve(plusConstraints);
        final ImmutableMap<String, BigInteger> solutionMinus =
            this.consSysSolver.solve(minusConstraints);

        if (solutionPlus == null || solutionMinus == null) {
            return null;
        }

        final ArrayList<SimplePolynomial> tPlus = new ArrayList<>();

        for (int i = 0; i < b.size(); i++) {
            final BigInteger n =
                solutionPlus.get(InterpolationSolver.constraintIdentifier(a.size() + i));

            if (n!=null && !n.equals(BigInteger.ZERO)) {
                tPlus.add(b.get(i).getPolynomial().times(n));
            }
        }

        final ArrayList<SimplePolynomial> tMinus = new ArrayList<>();

        for (int i = 0; i < a.size(); i++) {

            final BigInteger n =
                solutionMinus.get(InterpolationSolver.constraintIdentifier(i));

            if (n != null && !n.equals(BigInteger.ZERO)) {
                tMinus.add(a.get(i).getPolynomial().times(n));

            }
        }
        return new Pair<>(
            SimplePolynomial.plus(tPlus).plus(SimplePolynomial.create(y)), SimplePolynomial
            .plus(tMinus)
            .plus(SimplePolynomial.create(x)));
        }


    /**
     * @param a constraints system
     * @param b constraints system
     * @return true if a implies b, false otherwise
     */
    synchronized public boolean isImplied(
        final PolyConstraintsSystem a,
        final PolyConstraintsSystem b)
    {

        if (a.equals(b)) {
            return true;
        }

        if (a.isTrue()) {
            return b.isTrue();
        }

        if (a.isFalse()) {
            return true;
        }
        if (b.isFalse()) {
            return a.isFalse();
        }

        if (a.contains(b)) {
            return true;
        }

        return this.consSysSolver.implies(a, b);
    }

    /**
     * @param a
     * @param b
     * @return true if a implies b, false otherwise
     */
    synchronized public boolean isImplied(final PolyDisjunction a, final PolyDisjunction b)
    {
        final Pair pair = new Pair<>(a.clone(), b.clone());

        if (this.IMPLIES_NONNEG.containsKey(pair)) {
            return this.IMPLIES_NONNEG.get(pair);
        }


        boolean result;
        if ((a.isTrue() && !b.isTrue())|| (!a.isEmpty() && b.isEmpty()))
        {
            result = false;
        } else if (a.isEmpty() || b.isTrue() || b.getConstraintsSystems().containsAll(a.getConstraintsSystems())) {
            result = true;
        } else if (!b.isTrue() && this.getCommonVariables(a, b).isEmpty()) {
            return false;
        } else {

            final PolyDisjunction bNegated = b.negate(); // this.disjSolver.negate(b); //negate(b);

            result = this.disjSolver.conjunction(a, bNegated).isEmpty();

        }

        this.IMPLIES_NONNEG.put(pair, result);

        return result;
    }



    /**
     * @param a
     * @param b
     * @return common variables of a and b
     */
    private Set<String> getCommonVariables(final PolyDisjunction a, final PolyDisjunction b) {
        final Set<String> commonVars = new HashSet<>();
        commonVars.addAll(this.disjSolver.getVariables(a));
        commonVars.retainAll(this.disjSolver.getVariables(b));
        return commonVars;
    }

    /**
     * @param list - collection of disjunctions of general systems
     * @return - set of variables appearing in the list
     */
    public HashSet<String> getVariables(final Collection<PolyDisjunction> list) {
        final HashSet<String> vars = new HashSet<>();

        for (final PolyDisjunction d : list) {
            vars.addAll(this.disjSolver.getVariables(d));
        }

        return vars;
    }

    private Pair<PolyDisjunction, PolyDisjunction> restrict(final Pair<PolyDisjunction, PolyDisjunction> pair)
    {
        final PolyDisjunction aOriginal = pair.x;
        final PolyDisjunction bOriginal = pair.y;

        Pair<PolyDisjunction, PolyDisjunction> result = null;

        if (aOriginal.isEmpty() || bOriginal.isEmpty()) {
            result = new Pair<>(PolyDisjunction.FALSE, PolyDisjunction.FALSE);
        } else {

            Set commonVars = this.getCommonVariables(aOriginal, bOriginal);

            PolyDisjunction a = this.disjSolver.restrict(aOriginal, commonVars);

            PolyDisjunction b = this.disjSolver.restrict(bOriginal, commonVars);

            if (!commonVars.isEmpty()) {

                commonVars = this.getCommonVariables(a, b);

                PolyDisjunction aN = this.disjSolver.restrict(aOriginal, commonVars);

                while (!a.getConstraintsSystems().containsAll(aN.getConstraintsSystems())) {
                    a = aN;

                    commonVars = this.getCommonVariables(a, aOriginal);

                    aN = this.disjSolver.restrict(aOriginal, commonVars);
                }

                commonVars = this.getCommonVariables(b, bOriginal); // Tools.intersect(b.getVariables(), bOriginal.getVariables());

                PolyDisjunction bN = this.disjSolver.restrict(bOriginal, commonVars);

                while (!b.getConstraintsSystems().containsAll(bN.getConstraintsSystems())) {
                    b = bN;

                    commonVars = this.getCommonVariables(b, bOriginal); //  Tools.intersect(b.getVariables(), bOriginal.getVariables());

                    bN = this.disjSolver.restrict(bOriginal, commonVars);
                }
            }
            result = new Pair<>(a, b);
        }

        return result;
    }


    synchronized private  Pair<PolyConstraintsSystem, PolyConstraintsSystem> restrictToCommonVariables(
        final Pair<PolyConstraintsSystem, PolyConstraintsSystem> pair)

        {

        if (this.RESTRICTED.containsKey(pair)) {
            return this.RESTRICTED.get(pair);
        }

        final PolyConstraintsSystem aOriginal = pair.x;
        final PolyConstraintsSystem bOriginal = pair.y;

        Pair<PolyConstraintsSystem, PolyConstraintsSystem> result = null;

        if (aOriginal.isEmpty() || bOriginal.isEmpty()) {
            result = new Pair<>(PolyConstraintsSystem.create(), PolyConstraintsSystem.create());
        } else {

            Set commonVars = this.getCommonVariables(aOriginal, bOriginal); // Tools.intersect(aOriginal.getVariables(), bOriginal.getVariables());

            PolyConstraintsSystem a = this.consSysSolver.restrictVariables(aOriginal, commonVars);

            PolyConstraintsSystem b = this.consSysSolver.restrictVariables(bOriginal, commonVars);

            if (!commonVars.isEmpty()) {

                commonVars = this.getCommonVariables(a, aOriginal); //Tools.intersect(a.getVariables(), aOriginal.getVariables());

                PolyConstraintsSystem aN = this.consSysSolver.restrictVariables(aOriginal, commonVars);

                while (!a.contains(aN)) {
                    a = aN;

                    commonVars = this.getCommonVariables(a, aOriginal); // // Tools.intersect(a.getVariables(), aOriginal.getVariables());

                    aN = this.consSysSolver.restrictVariables(aOriginal, commonVars);
                }

                commonVars = this.getCommonVariables(b, bOriginal); //Tools.intersect(b.getVariables(), bOriginal.getVariables());

                PolyConstraintsSystem bN = this.consSysSolver.restrictVariables(bOriginal, commonVars);

                while (!b.contains(bN)) {
                    b = bN;

                    commonVars = this.getCommonVariables(b, bOriginal); //Tools.intersect(b.getVariables(), bOriginal.getVariables());

                    bN = this.consSysSolver.restrictVariables(bOriginal, commonVars);
                }
            }
            result = new Pair<>(a, b);
            final Pair<PolyConstraintsSystem, PolyConstraintsSystem> pair2 = new Pair<>(pair.y, pair.x);
            this.RESTRICTED.put(pair, result);
            this.RESTRICTED.put(pair2, result);
        }

        return result;

        }

    private Set getCommonVariables(final PolyConstraintsSystem a, final PolyConstraintsSystem b) {
        return this.getCommonVariables(PolyDisjunction.create(a), PolyDisjunction.create(b));
    }

    public PolyDisjunction restrict(final PolyDisjunction disj, final Set<String> vars) {
        PolyDisjunction result = PolyDisjunction.FALSE;

        for (final PolyConstraintsSystem constSys : disj.getConstraintsSystems()) {
            final PolyConstraintsSystem restSys = this.consSysSolver.restrictVariables(constSys, vars);

            if (!restSys.isEmpty()) {
                result = result.addSystem(restSys);
            }
        }

        final Set<String> newVars = this.disjSolver.getVariables(result);

        if (!vars.containsAll(newVars)) {
            return this.restrict(disj,newVars);
        }

        return result;
    }

    /**
     * @param seq
     * @param varToF
     * @return
     */
    private Set<List<LinearConstraintsSystem>> split(
        final List<LinearConstraintsSystem> seq,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF)
        {

        final Map<String,Set<String>> nameToGroup = new HashMap<>();

        for (final LinearConstraintsSystem item : seq) {
            for (final SimplePolyConstraint constraint : item.getConstraints()) {
                final Set<String> refered = new HashSet<>();
                refered.addAll(this.getReferedIds(constraint, varToF));

                for (final String name : new HashSet<>(refered)) {
                    if (nameToGroup.containsKey(name)) {
                        refered.addAll(nameToGroup.get(name));
                    }
                }

                for (final String name : refered) {
                    nameToGroup.put(name, refered);
                }
            }
        }

        final Set<List<LinearConstraintsSystem>> result = new HashSet<>();

        for (final Set<String> group : new HashSet<>(nameToGroup.values())) {
            final List<LinearConstraintsSystem> subSeq = new ArrayList<>();

            for (final LinearConstraintsSystem item : seq) {
                final Set<SimplePolyConstraint> constraints = new HashSet<>();

                for (final SimplePolyConstraint c : item.getConstraints()) {
                    if (group.containsAll(this.getReferedIds(c, varToF))) {
                        constraints.add(c);
                    }
                }

                subSeq.add(LinearConstraintsSystem.create(constraints));
            }

            result.add(subSeq);
        }


        return result;
        }

    /**
     * @param seq
     * @param varToF
     * @return
     */
    private List<LinearConstraintsSystem> reduce(
        final List<LinearConstraintsSystem> seq,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF)
        {

        List<LinearConstraintsSystem> currSeq = seq;


        boolean reduced;

        do {
            reduced = false;
            final List<LinearConstraintsSystem> subSeq = new ArrayList<>();

            final Map<String, Integer> refCount = new HashMap<>();

            for (final LinearConstraintsSystem item : currSeq) {
                for (final SimplePolyConstraint constraint : item.getConstraints()) {
                    for (final String var : this.getReferedIds(constraint, varToF)) {
                        final String name = var;

                        if (!refCount.containsKey(name)) {
                            refCount.put(var, 0);
                        }

                        refCount.put(name, refCount.get(name) + 1);
                    }
                }
            }

            final Set<String> toRemove = new HashSet<>();

            for (final Entry<String, Integer> entry : refCount.entrySet()) {
                if (entry.getValue() < 2) {
                    toRemove.add(entry.getKey());
                }
            }

            final Set<SimplePolyConstraint> previous = new HashSet<>();

            for (final LinearConstraintsSystem item : currSeq) {
                final Set<SimplePolyConstraint> constraints = new HashSet<>();

                for (final SimplePolyConstraint c : item.getConstraints()) {
                    SimplePolyConstraint constraint = c;

                    if (constraint.isSatisfiable()) {
                        boolean skip = previous.contains(constraint);

                        if (!skip && constraint.getType().equals(ConstraintType.EQ)) {
                            final SimplePolyConstraint a =
                                new SimplePolyConstraint(constraint.getPolynomial(), ConstraintType.GE);
                            final SimplePolyConstraint b =
                                new SimplePolyConstraint(constraint.getPolynomial().negate(), ConstraintType.GE);

                            if (previous.contains(a)) {
                                constraint = b;
                            } else if (previous.contains(b)) {
                                constraint = a;
                            }

                            skip = previous.contains(constraint);
                        }

                        if (!skip) {
                            for (final String var : this.getReferedIds(constraint, varToF)) {
                                if (toRemove.contains(var)) {
                                    skip = true;
                                    break;
                                }
                            }
                        }

                        if (!skip) {

                            constraints.add(c);
                        } else {
                            //   Log.report("Interpolate", "Remove: " + c);
                        }

                        reduced = reduced || skip;

                    }

                }

                previous.addAll(LinearConstraintsSystem.create(constraints).toGeConstraintsSystem().getConstraints());

                subSeq.add(LinearConstraintsSystem.create(constraints));
            }

            currSeq = subSeq;
        } while (reduced);

        return currSeq;

        }

    private final Map<SimplePolyConstraint, ImmutableSet<String>> REF_IDS = new HashMap<>();

    private Set<String> getReferedIds(
        final SimplePolyConstraint constraint,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF)
        {

        if (!this.REF_IDS.containsKey(constraint)) {

            final Set<String> ids = new HashSet<>();

            final ProcessingStack<String> procStack = new ProcessingStack<>(constraint.getPolynomial().getVariables());

            while (!procStack.isEmpty()) {
                final String variable = procStack.pop();
                if (varToF.containsKey(variable)) {
                    final Pair<TRSFunctionApplication, List<String>> pair = this.varToF.get(variable);
                    procStack.pushAll(pair.y);
                    ids.add(pair.x.getRootSymbol().getName());
                } else {
                    procStack.push(variable);
                    ids.add(variable);
                }
            }

            this.REF_IDS.put(constraint, ImmutableCreator.create(ids));

        }
        return this.REF_IDS.get(constraint);
        }

    public List<LinearDisjunction> solve(
        final ImmutableList<LinearConstraintsSystem> seq)
        {

        final List<LinearConstraintsSystem> subSeq = this.reduce(seq, this.varToF);

        final Set<List<LinearConstraintsSystem>> splited = this.split(subSeq, this.varToF);

        for (final List<LinearConstraintsSystem> splitSeq : splited) {
            final List<LinearDisjunction> inter =
                this.solveSubSeq(ImmutableCreator.create(splitSeq), this.fSymToVar, this.varToF, this.ng);

            if (inter != null) {
                return inter;
            }
        }

        return null;
        }

    /**
     * @param constraintsSys list of constraints systems
     * @param fSymToVar
     * @param ng
     * @return list of appropriate interpolant if could be found, null otherwise
     */
    public List<LinearDisjunction> solveSubSeq(
        final ImmutableList<LinearConstraintsSystem> constraintsSys,
        final Map<FunctionSymbol, Set<String>> fSymToVar,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF,
        final FreshNameGenerator ng)
        {
        // empty list can't have an interpolant
        if (constraintsSys.isEmpty()) {
            return null;
        }

        // in case we ended up (or started with) having a single item in our list
        if (constraintsSys.size() == 1) {
            if (!this.consSysSolver.isSAT(constraintsSys.get(0))) {
                return Arrays.asList(LinearDisjunction.TRUE, LinearDisjunction.FALSE);
            }
            return null;
        }

        // try reduce the list of constraints systems
        List<LinearConstraintsSystem> nodupPath = new ArrayList<>();

        for (int i = 0; i < constraintsSys.size(); i++) {
            final LinearConstraintsSystem item = constraintsSys.get(i);

            //  True or duplicate systems have nothing to contribute here
            if (!item.isTrue() && !nodupPath.contains(item)) {
                nodupPath.add(item);
            }
        }

        if (this.PATH_CONSTRAINTS_INTERPOLATION.containsKey(nodupPath)) {
            final List<LinearDisjunction> nodupInter = this.PATH_CONSTRAINTS_INTERPOLATION.get(nodupPath);
            if (nodupInter == null) {
                // already tried, nothing to do here
                return null;
            } else {
                // stretch the previously found interpolation list to fit the constraints systes list
                final ArrayList<LinearDisjunction> inter = new ArrayList<>();
                ;
                for (int current = 0, i = 0; i < nodupPath.size(); i++) {
                    final int index = constraintsSys.indexOf(nodupPath.get(i));

                    for (int j = current; j <= index; j++) {
                        inter.add(nodupInter.get(i));
                    }
                    current = index + 1;
                }

                while (inter.size() <= constraintsSys.size()) {
                    inter.add(LinearDisjunction.FALSE);
                }

                // done
                return inter;
            }
        }

        boolean matchFound = false;

        // try find a couple of constraints systems where the first one implies the negation of the second one
        for (int i = 0; i < nodupPath.size(); i++) {
            for (int j = i + 1; j < nodupPath.size(); j++) {
                if (this.isImplied(PolyDisjunction.create(nodupPath.get(i)), nodupPath.get(j).negate())) {
                    matchFound = true;
                    nodupPath = Arrays.asList(nodupPath.get(i), nodupPath.get(j));
                    break;
                }
            }
            if (matchFound) {
                break;
            }
        }

        matchFound = false;

        // try imply previously found results on the current constraints list
        for (final ImmutableList<LinearConstraintsSystem> p : this.PATH_CONSTRAINTS_INTERPOLATION.keySet()) {
            final List<LinearDisjunction> inter = this.PATH_CONSTRAINTS_INTERPOLATION.get(p);
            if (inter != null && nodupPath.containsAll(p) && nodupPath.size() < p.size()) {
                // the current list contains (as a set) a previously proven list, therefore it's enough to concentrate on it's sublist

                int startPos = nodupPath.size() - 1;
                int endPos = 0;

                for (int i = 0; i < p.size(); i++) {
                    final int index = nodupPath.indexOf(p.get(i));

                    if (index > endPos) {
                        endPos = index;
                    }

                    if (index < startPos) {
                        startPos = index;
                    }
                }

                nodupPath = new ArrayList(nodupPath.subList(0, endPos + 1)); //startpos-> 0
                matchFound = true;
            } else if (inter == null && p.containsAll(nodupPath)) {
                // already tried, nothing to do here
                this.PATH_CONSTRAINTS_INTERPOLATION.put(constraintsSys, null);
                return null;
            }

            if (matchFound) {
                break;
            }
        }




        // find the first infeasible constraints system in the list
        PolyConstraintsSystem current;
        int index = 0;
        for (index = 0, current = PolyConstraintsSystem.TRUE; index < nodupPath.size()
            && this.consSysSolver.isSAT(current); index++)
        {
            current = this.consSysSolver.conjunction(current, nodupPath.get(index));
        }


        //        if (this.consSysSolver.isSAT(current)) {
        //            // could not find an infeasible system, nothing to do here
        //            this.PATH_CONSTRAINTS_INTERPOLATION.put(constraintsSys, null);
        //
        //            Log.report("sol", this.consSysSolver.solve(current).toString());
        //
        //            return null;
        //        }

        //       // From here we can be 100% sure that the list has an interpolant

        int startPos = 0;
        final int endPos = index;
        final ArrayList<PolyConstraintsSystem> tail = new ArrayList<>();

        // prepare tail conjunctions
        for (int i = endPos - 1; i >= 1; i--) {
            if (tail.isEmpty()) {
                tail.add(nodupPath.get(i));
            } else {
                tail.add(tail.get(tail.size() - 1).merge(nodupPath.get(i)));
            }
        }

        Collections.reverse(tail);

        /* while (tail.get(startPos).isEmpty() && startPos < endPos) {
        startPos++;
        }*/

        startPos = 1;

        /*
        while (tail.get(endPos).isTrue() && endPos >= startPos) {
        endPos--;
        }
         */

        //        if (startPos == 0) {
        //            final int k = 0;
        //        }

        // we only need to interpolate till the first infeasible system
        // nodupPath = new ArrayList<>(nodupPath.subList(startPos - 1, endPos));
        // tail = new ArrayList<>(tail.subList(startPos, endPos));

        final ArrayList<LinearDisjunction> nodupInter = new ArrayList<>();
        nodupInter.add(LinearDisjunction.TRUE);

        for (int i = 0; i < nodupPath.size(); i++) {
            LinearDisjunction head = nodupInter.get(i).addToAll(nodupPath.get(i));

            if (this.disjSolver.isUNSAT(head)) {
                head = LinearDisjunction.create(false);
            }
            //                LinearDisjunction.create(this.disjSolver.conjunction(
            //                    nodupInter.get(i),
            //                    LinearDisjunction.create(nodupPath.get(i))));


            if (i == nodupPath.size() - 1 || head.isEmpty()) {
                if (nodupInter.get(i).isTrue() || !head.isEmpty()) {
                    return null;
                }


                // last and infeasible items don't need to be interpolated
                nodupInter.add(head);
                continue;
            }


            final PolyConstraintsSystem currTail = tail.get(i);
            // this.consSysSolver.restrictVariables(tail.get(i), this.consSysSolver.getVariables(head));
            //                this.disjSolver
            //                    .restrict(PolyDisjunction.create(), this.consSysSolver.getVariables(head))
            //                    .getConstraintsSystems()
            //                    .iterator()
            //                    .next();

            LinearDisjunction currInter =
                this.solve(head, LinearDisjunction.create(PolyDisjunction.create(currTail)), fSymToVar, varToF, ng);

            // if no interpolant was found
            if (currInter == null) {
                currInter = LinearDisjunction.TRUE;
            }

            nodupInter.add(currInter);
        }

        // stretch the resulted interpolant to fit the original constraints systems list
        final ArrayList<LinearDisjunction> inter = new ArrayList<>();

        int curr = 0;
        for (int i = 0; i < nodupPath.size(); i++) {
            final int ind = constraintsSys.indexOf(nodupPath.get(i));

            for (int j = curr; j <= ind; j++) {
                inter.add(nodupInter.get(i));
            }

            curr = ind + 1;
        }

        while (inter.size() <= constraintsSys.size()) {
            inter.add(LinearDisjunction.FALSE);
        }

        final ArrayList<LinearConstraintsSystem> reducedPath = new ArrayList<>();
        final ArrayList<LinearDisjunction> reducedInter = new ArrayList<>();
        reducedInter.add(LinearDisjunction.TRUE);

        for (int i = 0; i < constraintsSys.size(); i++) {
            final LinearDisjunction f = inter.get(i + 1);

            if (!reducedInter.contains(f)) {
                reducedInter.add(f);

                reducedPath.add(constraintsSys.get(i));

            }
        }


        if (Globals.useAssertions) {
            assert reducedInter.get(reducedInter.size() - 1).isEmpty();
        } else {
            // something went terribly wrong
            if (!reducedInter.get(reducedInter.size() - 1).isEmpty()) {
                return null;
            }
        }

        // save results for future generations
        this.PATH_CONSTRAINTS_INTERPOLATION.put(
            ImmutableCreator.create(reducedPath),
            ImmutableCreator.create(reducedInter));

        return ImmutableCreator.create(inter);
        }

    /**
     * @param a
     * @param b
     * @param fSymToVar
     * @param varToF
     * @param ng
     * @return
     */
    private LinearDisjunction solve(
        final LinearDisjunction a,
        final LinearDisjunction b,
        final Map<FunctionSymbol, Set<String>> fSymToVar,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF,
        final FreshNameGenerator ng)
    {

        final Pair<PolyDisjunction, PolyDisjunction> pair = new Pair<PolyDisjunction, PolyDisjunction>(a, b);

        synchronized (this.SOLUTION_DisjunctionGeneralConstraintsSystem) {
            if (this.SOLUTION_DisjunctionGeneralConstraintsSystem.containsKey(pair)) {
                return LinearDisjunction.create(this.SOLUTION_DisjunctionGeneralConstraintsSystem.get(pair));
            }
        }

        PolyDisjunction result = PolyDisjunction.FALSE;

        for (final LinearConstraintsSystem systemA : a.getLinearConstraintsSystems()) {
            PolyDisjunction interpolant = PolyDisjunction.create();
            for (final LinearConstraintsSystem systemB : b.getLinearConstraintsSystems()) {
                final LinearDisjunction item = this.solve(systemA, systemB, fSymToVar, varToF, ng);
                if (item != null) {
                    interpolant = interpolant.mergeAll(item);
                }
            }
            if (!interpolant.isEmpty()) {
                result = result.addAllSystems(interpolant.getConstraintsSystems());
            }
        }

        this.SOLUTION_DisjunctionGeneralConstraintsSystem.put(pair, (PolyDisjunction) result.clone());
        return LinearDisjunction.create(result);

    }

    /**
     * @param systemA
     * @param systemB
     * @param fSymToVar
     * @param varToF
     * @param ng
     * @return
     */
    private LinearDisjunction solve(
        final LinearConstraintsSystem systemA,
        final LinearConstraintsSystem systemB,
        final Map<FunctionSymbol, Set<String>> fSymToVar,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF,
        final FreshNameGenerator ng)
    {
        final Set<Pair<String, String>> fPairs = new HashSet<>();

        for (final Entry<FunctionSymbol, Set<String>> fs : fSymToVar.entrySet()) {
            for (final String a : fs.getValue()) {
                for (final String b : fs.getValue()) {
                    if (a.equals(b) || fPairs.contains(new Pair<>(b, a))) {
                        continue;
                    }
                    fPairs.add(new Pair<>(a, b));
                }
            }
        }
        return this.solve(systemA, systemB, fPairs, varToF, ng);
    }

    /**
     * @param id - constraint id
     * @return corresponding variable name
     */
    private static String createConstraintIdentifier(final int id) {
        return "c" + id;
    }

    /**
     * The constraints turn into the variables, each variable gets a constraint (not including the numerical addend)
     * @param numericalAddend - values for numerical addend
     * @param constraintType - constraint type
     * @param lowerBounds - lower bounds (if exist)
     * @param upperBounds - upper bounds (if exist)
     * @return transposed system
     */
    public LinearConstraintsSystem transpose(
        final LinearConstraintsSystem linSys,
        final HashMap<IndefinitePart, BigInteger> numericalAddend,
        final ConstraintType constraintType,
        final HashMap<Integer, BigInteger> lowerBounds,
        final HashMap<Integer, BigInteger> upperBounds)
    {

        final HashSet<SimplePolyConstraint> result = new HashSet<>();

        for (final String id : linSys.getVariables()) {

            final ArrayList<SimplePolynomial> polySet = new ArrayList<>();

            int i = 0;
            for (int c = 0; c < linSys.getConstraints().size(); c++) {

                final BigInteger n =
                    linSys.get(c).getPolynomial().getSimpleMonomials().get(IndefinitePart.create(id, 1));
                if (n != null && !n.equals(BigInteger.ZERO)) {
                    final SimplePolynomial poly = SimplePolynomial.create(InterpolationSolver.constraintIdentifier(i)).times(n.negate());
                    polySet.add(poly);
                }
                i++;
            }

            final IndefinitePart indef = IndefinitePart.create(id, 1);
            if (numericalAddend != null && numericalAddend.containsKey(indef)) {
                polySet.add(SimplePolynomial.create(numericalAddend.get(indef)));
            }

            result.add(new SimplePolyConstraint(SimplePolynomial.plus(polySet), constraintType));
        }

        for (int j = 0; j < linSys.getConstraints().size(); j++) {
            if (lowerBounds != null && lowerBounds.containsKey(j)) {
                result.add(this.getVariableConstraint(InterpolationSolver.constraintIdentifier(j), BigInteger.ONE, lowerBounds
                    .get(j)
                    .negate(), ConstraintType.GE));
            }

            if (upperBounds != null && upperBounds.containsKey(j)) {
                result.add(this.getVariableConstraint(
                    InterpolationSolver.constraintIdentifier(j),
                    BigInteger.ONE.negate(),
                    upperBounds.get(j),
                    ConstraintType.GE));
            }
        }

        return new LinearConstraintsSystem(result);
    }

    /**
     * Create polynomial out of the numerical addend, the constraints turn into variables
     * @return polynomial with the addend values as coefficients
     */
    public SimplePolynomial transposeAddend(final LinearConstraintsSystem linSys) {
        final HashSet<SimplePolynomial> polySet = new HashSet<>();

        int i = 0;
        for (final SimplePolyConstraint c : linSys.getConstraints()) {

            final BigInteger n = c.getPolynomial().getNumericalAddend();

            final SimplePolynomial poly = SimplePolynomial.create(InterpolationSolver.constraintIdentifier(i)).times(n);
            polySet.add(poly);
            i++;
        }

        return SimplePolynomial.plus(polySet);
    }

    /**
     * Get constraints, all variables are non negative
     */
    public PolyConstraintsSystem getAllVariablesNonNegativeConstraints(final LinearConstraintsSystem linSys) {
        final HashSet<SimplePolyConstraint> result = new HashSet<>();

        for (final String id : linSys.getVariables()) {
            result.add(this.getVariableNonNegativeConstraint(id));
        }

        return PolyConstraintsSystem.create(result);
    }

    /**
     * Add constraint: id >= 0
     * @param id - variable name
     */
    public SimplePolyConstraint getVariableNonNegativeConstraint(final String id) {
        return this.getVariableConstraint(id, BigInteger.ONE, BigInteger.ZERO, ConstraintType.GE);
    }

    /**
     * get constraint: id x factor + addend (== , >=)
     *
     * @param id - variable name
     * @param factor - factor
     * @param addend - addend
     * @param constraintType - constraint type
     * @return
     */
    public SimplePolyConstraint getVariableConstraint(
        final String id,
        final BigInteger factor,
        final BigInteger addend,
        final ConstraintType constraintType)
    {
        return new SimplePolyConstraint(
            SimplePolynomial.create(id).times(factor).plus(SimplePolynomial.create(addend)),
            constraintType);
    }

    /**
     * @param id - constraint index
     * @return corresponding variable name
     */
    public static String constraintIdentifier(final int id) {
        return ("x" + id);
    }


    public static List<TRSTerm> solve(final List<TRSTerm> seq, final Abortion aborter) {

        final Map<String, Pair<TRSFunctionApplication, List<String>>> varToF = new HashMap<>();
        final Map<FunctionSymbol, Set<String>> fSymToVar = new HashMap<>();
        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);

        final List<LinearConstraintsSystem> linSeq = new ArrayList<>();

        for (final TRSTerm t : seq) {
            linSeq.add(TermTools.flattenConstraintsSystem(t, fSymToVar, varToF, ng));
        }

        final InterpolationSolver solver = InterpolationSolver.create(fSymToVar, varToF, ng, aborter);

        final List<LinearDisjunction> linInter =
            solver.solve(ImmutableCreator.create(linSeq));

        if (linInter == null) {
            return null;
        }

        final Map<TRSVariable, TRSTerm> map = new HashMap<>();

        for (final Entry<String, Pair<TRSFunctionApplication, List<String>>> entry : varToF.entrySet()) {
            map.put(TRSTerm.createVariable(entry.getKey()), entry.getValue().x);
        }

        final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(map));

        final List<TRSTerm> inter = new ArrayList<>();

        for (final LinearDisjunction l : linInter) {
            inter.add(l.toTerm().applySubstitution(sigma));
        }

        return inter;
    }

    private final Map<Pair<LinearConstraintsSystem, LinearConstraintsSystem>, SimplePolyConstraint> SOLUTION_SimplePolyConstraint =
        new HashMap<>();

        private final Map<Pair<PolyConstraintsSystem, PolyConstraintsSystem>, PolyConstraintsSystem> SOLUTION_GeneralConstraintsSystem =
            new HashMap<>();

            private final Map<Pair<PolyDisjunction, PolyDisjunction>, PolyDisjunction> SOLUTION_DisjunctionGeneralConstraintsSystem =
                new HashMap<>();

                private final Map<Pair<LinearDisjunction, LinearDisjunction>, LinearDisjunction> SOLUTION_DisjunctionLinearConstraintsSystem =
                    new HashMap<>();

                    private final Map<Pair<PolyDisjunction, PolyDisjunction>, Boolean> IMPLIES = new HashMap<>();

                    private final Map<Pair<PolyDisjunction, PolyDisjunction>, Boolean> IMPLIES_NONNEG = new HashMap<>();

                    private final Map<PolyDisjunction, PolyDisjunction> NEGATION = new HashMap<>();

                    private final Map<PolyDisjunction, ImmutableSet<String>> DISJUNCTION_VARIABLES = new HashMap<>();
                    private final Map<PolyConstraintsSystem, ImmutableSet<String>> CONSTRAINT_VARIABLES = new HashMap<>();

                    private final Map<Pair<PolyConstraintsSystem, PolyConstraintsSystem>, Pair<PolyConstraintsSystem, PolyConstraintsSystem>> RESTRICTED =
                        new HashMap<>();

                        private final Map<ImmutableList<PolyDisjunction>, ImmutableList<PolyDisjunction>> PATH_INTERPOLATION =
                            new HashMap<>();

                            private final Map<ImmutableList<LinearConstraintsSystem>, ImmutableList<LinearDisjunction>> PATH_CONSTRAINTS_INTERPOLATION =
                                new HashMap<>();

                                private final Map<ImmutableList<TRSTerm>, ImmutableList<TRSTerm>> PATH_TERMS_INTERPOLATION = new HashMap<>();

                                public ConstraintsSystemSolver getConstraintsSystemSolver() {
                                    return this.consSysSolver;
                                }

                                public DisjunctionSolver getDisjunctionSolver() {
                                    return this.disjSolver;
                                }



}
