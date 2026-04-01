package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.SMT.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class ConstraintInformation implements Immutable {

    /**
     * Assume pol = 0 holds and pol has the form "-x + pol2" for some variable x
     * and some remaining polynomial pol2. Then return "x = - pol2". Otherwise
     * return null. If possible, return assignments of variables in v
     * @param pol
     * @param v variables to try first.
     * @return
     */
    private static Pair<String, SimplePolynomial> createAssignment(final SimplePolynomial pol, final Set<String> v) {
        LinkedHashSet<String> indefs = new LinkedHashSet<>();
        // LinkedHashSets will be traversed in insertion order. This prefers the variables from v.
        indefs.addAll(v);
        indefs.addAll(pol.getIndefinites());

        for (String var : indefs) {
            SimplePolynomial vp = SimplePolynomial.create(var);
            SimplePolynomial pol2 = pol.plus(vp);
            if (!pol2.containsIndefinite(var)) {
                return new Pair<>(var, pol2);
            }
            SimplePolynomial npol2 = pol.minus(SimplePolynomial.create(var));
            if (!npol2.containsIndefinite(var)) {
                return new Pair<>(var, npol2.negate());
            }
        }
        return null;
    }

    /**
     * Pairs (x, t), such that x = t holds. The keySet of equalities and the set
     * of variables in t are disjoint.
     */
    private final ImmutableLinkedHashMap<TRSVariable, TRSTerm> equalities;
    /**
     * Terms t, such that t >= 0 holds. None of these terms contains variables
     * in the keySet of equalities.
     */
    private final ImmutableLinkedHashSet<TRSTerm> inequalities;
    private final ImmutableLinkedHashSet<Constraint> unhandledConstraints;

    /**
     * Resolves polynomial equalities transitively.
     * @param constraints
     * @param vars Set of variables to try to instantiate in equalities
     */
    public ConstraintInformation(final ImmutableSet<Constraint> constraints, Set<TRSVariable> vars) {
        LinkedHashSet<SimplePolynomial> ineqs = new LinkedHashSet<>();
        LinkedHashSet<Constraint> unhandledConstrs = new LinkedHashSet<>();
        LinkedHashSet<String> v = new LinkedHashSet<>();
        for (TRSVariable var : vars) {
            v.add(var.getName());
        }

        for (Constraint c : constraints) {
            try {
                ineqs.addAll(c.computePolynomials());
            } catch (NotRepresentableAsPolynomialsException e) {
                unhandledConstrs.add(c);
            }
        }
        this.unhandledConstraints = ImmutableCreator.create(unhandledConstrs);

        Map<String, SimplePolynomial> eqs = new LinkedHashMap<>();
        while (true) {
            // find equality
            SimplePolynomial geqZero = null;
            SimplePolynomial leqZero = null;
            Pair<String, SimplePolynomial> assg = null;
            for (SimplePolynomial pol : ineqs) {
                geqZero = pol;
                leqZero = geqZero.negate();
                if (ineqs.contains(leqZero)) {
                    assg = ConstraintInformation.createAssignment(pol, v);
                    if (assg != null) {
                        break;
                    }
                }
            }
            if (assg == null) {
                break;
            }
            Map<String, SimplePolynomial> map = new LinkedHashMap<>();
            map.put(assg.x, assg.y);
            ineqs.remove(geqZero);
            ineqs.remove(leqZero);
            // refine ineqs and eqs
            LinkedHashSet<SimplePolynomial> newineqs = new LinkedHashSet<>();
            for (SimplePolynomial ineq : ineqs) {
                newineqs.add(ineq.substitute(map));
            }
            ineqs = newineqs;
            Map<String, SimplePolynomial> neweqs = new LinkedHashMap<>();
            for (Entry<String, SimplePolynomial> entry : eqs.entrySet()) {
                neweqs.put(entry.getKey(), entry.getValue().substitute(map));
            }
            eqs = neweqs;
            eqs.put(assg.x, assg.y);
        }
        LinkedHashMap<TRSVariable, TRSTerm> reqs = new LinkedHashMap<>();
        for (Entry<String, SimplePolynomial> entry : eqs.entrySet()) {
            TRSVariable x = TRSTerm.createVariable(entry.getKey());
            TRSTerm t = CpxIntTermHelper.fromSimplePolynomial(entry.getValue());
            if (x.equals(t)) {
                continue;
            }
            reqs.put(x, t);
        }
        this.equalities = ImmutableCreator.create(reqs);
        LinkedHashSet<TRSTerm> rineqs = new LinkedHashSet<>();
        for (SimplePolynomial pol : ineqs) {
            BigInteger b = pol.getConstantSize();
            if (b != null && b.compareTo(BigInteger.ZERO) >= 0) {
                continue;
            }
            TRSTerm t = CpxIntTermHelper.fromSimplePolynomial(pol);
            rineqs.add(t);
        }
        this.inequalities = ImmutableCreator.create(rineqs);
    }

    public ImmutableMap<TRSVariable, TRSTerm> getEqualities() {
        return this.equalities;
    }

    public ImmutableSet<TRSTerm> getInequalities() {
        return this.inequalities;
    }

    public ImmutableSet<Constraint> getUnhandledConstraints() {
        return this.unhandledConstraints;
    }

    /**
     * Skips nonlinear constraints. Is there a useful linear approximation for
     * some linear stuff?
     * @param factory
     * @return
     */
    public Formula<SMTLIBTheoryAtom> getSMTLIBOverapproximation(FormulaFactory<SMTLIBTheoryAtom> factory) {
        List<Formula<SMTLIBTheoryAtom>> args = new ArrayList<>();

        for (Entry<TRSVariable, TRSTerm> eq : this.equalities.entrySet()) {
            try {
                SimplePolynomial pol = CpxIntTermHelper.toSimplePolynomial(eq.getValue());
                //                if (!pol.isLinear()) {
                //                    continue;
                //                }
                SMTLIBTheoryAtom constr =
                    SMTLIBIntEquals.create(SMTLIBIntVariable.create(eq.getKey().getName()), pol.toSMTLIB());
                args.add(factory.buildTheoryAtom(constr));
            } catch (NotRepresentableAsPolynomialException e) {
                continue;
            }
        }

        for (TRSTerm ineq : this.inequalities) {
            try {
                SimplePolynomial pol = CpxIntTermHelper.toSimplePolynomial(ineq);
                //                if (!pol.isLinear()) {
                //                    continue;
                //                }
                SMTLIBTheoryAtom constr = SMTLIBIntGE.create(pol.toSMTLIB(), SMTLIBIntConstant.create(BigInteger.ZERO));
                args.add(factory.buildTheoryAtom(constr));

            } catch (NotRepresentableAsPolynomialException e) {
                continue;
            }
        }

        return factory.buildAnd(args);
    }

    private static SMTSolverFactory FACTORY = new Z3ExtSolverFactory();

    public boolean isUnsatisfiable(Abortion aborter) throws AbortionException {
        if (this.isTrue()) {
            return false;
        }
        VariableScope scope = new VariableScope();
        SMTSolver solver = ConstraintInformation.FACTORY.getSMTSolver(SMTLIBLogic.QF_NIA, aborter);
        solver.addAssertion(this.getSMTOverapproximation(scope));
        YNM result = solver.checkSAT();
        try {
            solver.dispose();
        } catch (IOException e) {
            // we don't really care if disposing the solver did not work.
        }
        return YNM.NO.equals(result);
    }

    private boolean isTrue() {
        return this.equalities.isEmpty() && this.inequalities.isEmpty() && this.unhandledConstraints.isEmpty();
    }

    public TRSSubstitution computeSimplifyingSubstitution(Set<TRSVariable> variables) {
        Map<TRSVariable, TRSTerm> eqs = new LinkedHashMap<>();
        eqs.putAll(this.getEqualities());
        for (TRSVariable v : variables) {
            eqs.remove(v);
        }
        if (eqs.isEmpty()) {
            return TRSSubstitution.EMPTY_SUBSTITUTION;
        }
        TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(eqs));
        return sigma;
    }

    public SMTExpression<SBool> getSMTOverapproximation(VariableScope scope) {
        List<SMTExpression<SBool>> args = new ArrayList<>();

        for (Entry<TRSVariable, TRSTerm> eq : this.equalities.entrySet()) {
            try {
                SimplePolynomial pol = CpxIntTermHelper.toSimplePolynomial(eq.getValue());
                Symbol0<SInt> v = scope.intVar(eq.getKey().getName());
                args.add(Core.equivalent(pol.toSMT(scope), v));
            } catch (NotRepresentableAsPolynomialException e) {
                continue;
            }
        }

        for (TRSTerm ineq : this.inequalities) {
            try {
                SimplePolynomial pol = CpxIntTermHelper.toSimplePolynomial(ineq);
                args.add(Ints.greaterEqual(pol.toSMT(scope), Ints.constant(0)));
            } catch (NotRepresentableAsPolynomialException e) {
                continue;
            }
        }

        return Core.and(args);
    }

    public LinkedHashSet<Constraint> getConstraints() {
        LinkedHashSet<Constraint> cs = new LinkedHashSet<>();
        for (TRSTerm ineq : this.getInequalities()) {
            try {
                cs.add(Constraint.create(TRSTerm.createFunctionApplication(
                    CpxIntTermHelper.fGe,
                    ineq,
                    CpxIntTermHelper.ZERO)));
            } catch (NoConstraintTermException e) {
                throw new RuntimeException(e);
            }
        }
        for (Entry<TRSVariable, TRSTerm> eq : this.getEqualities().entrySet()) {
            try {
                cs.add(Constraint.create(TRSTerm.createFunctionApplication(
                    CpxIntTermHelper.fEq,
                    eq.getKey(),
                    eq.getValue())));
            } catch (NoConstraintTermException e) {
                throw new RuntimeException(e);
            }
        }
        for (Constraint c : this.getUnhandledConstraints()) {
            cs.add(c);
        }
        return cs;
    }
}
