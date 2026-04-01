package aprove.verification.complexity.CpxIntTrsProblem.Algorithms;

import java.io.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Macros.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.Factories.*;
import aprove.verification.oldframework.SMT.Solver.Z3.*;
import aprove.verification.oldframework.SMT.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class LocalSizeBoundComputation {

    static final Z3SolverFactory FACTORY = new Z3ExtSolverFactory();

    private static final LocalComplexityValue[] testedComplexities = {
        LocalComplexityValue.POL0,
        LocalComplexityValue.EQUALITYBOUND,
        LocalComplexityValue.ADDCONSTANTBOUND,
        LocalComplexityValue.ADDBOUND,
        LocalComplexityValue.POL1 };

    private static ImmutableLinkedHashSet<Integer> emptyA = ImmutableCreator.create(new LinkedHashSet<Integer>());

    public static LocalSizeBound computeLocalSizeBounds(CallArgument alpha, Abortion aborter) {
        SMTSolver solver = LocalSizeBoundComputation.FACTORY.getSMTSolver(SMTLIBLogic.QF_NIA, aborter);

        CpxIntTupleRule rule = alpha.rule;
        TRSTerm r_pi = alpha.getTerm();
        ImmutableArrayList<Integer> influence = LocalSizeBoundComputation.computeInfluencingArguments(r_pi, rule);
        VariableScope scope = new VariableScope();
        for (TRSVariable x : rule.getVariables()) {
            Symbol0<SInt> s = scope.intVar(x.getName());
            solver.declare(s);
        }
        Symbol0<SInt> r_pi_abs = Ints.intVar();
        solver.declare(r_pi_abs);
        solver.declare(IntMaxMacro.macro); // we want to use it often, so declare it beforehand
        try {
            solver.addAssertion(Core.equivalent(
                r_pi_abs,
                Ints.abs(CpxIntTermHelper.toSimplePolynomial(r_pi).toSMT(scope))));
        } catch (NotRepresentableAsPolynomialException e) {
            throw new RuntimeException(e);
        }
        ConstraintInformation ci = rule.getConstraintInformation();
        SMTExpression<SBool> phi = ci.getSMTOverapproximation(scope);
        solver.addAssertion(phi);
        LocalSizeBound best = new LocalSizeBound(LocalSizeBoundComputation.emptyA, LocalComplexityValue.UNBOUNDED, alpha);
        ImmutableList<TRSTerm> args = rule.getLeft().getArguments();
        for (ArrayList<Integer> l : new SublistEnumerator<>(influence)) {
            LinkedHashSet<Integer> rA = new LinkedHashSet<>();
            rA.addAll(l);
            ImmutableLinkedHashSet<Integer> A = ImmutableCreator.create(rA);
            ArrayList<SMTExpression<SInt>> abs_vars = new ArrayList<>();
            for (int i : l) {
                abs_vars.add(Ints.abs(scope.intVar(args.get(i).getName())));
            }
            for (LocalComplexityValue lc : LocalSizeBoundComputation.testedComplexities) {
                // test exactly POL0 without arguments
                if (lc.equals(LocalComplexityValue.POL0) != (l.size() == 0)) {
                    continue;
                }
                LocalSizeBound newLSB = new LocalSizeBound(A, lc, alpha);
                // only check if the test can improve our result
                if (newLSB.isBetter(best)) {
                    solver.push();
                    SMTExpression<SInt> c = lc.createSMTExpression(abs_vars);
                    solver.addAssertion(Ints.greater(r_pi_abs, c));
                    if (YNM.NO.equals(solver.checkSAT())) {
                        best = newLSB;
                    }
                    solver.pop();
                }
            }
        }
        try {
            solver.dispose();
        } catch (IOException e) {
            // we don't really care if disposing the solver did not work.
        }
        return best;
    }

    private static ImmutableArrayList<Integer> computeInfluencingArguments(TRSTerm t, CpxIntTupleRule rule) {
        ImmutableList<TRSTerm> lhsV = rule.getLeft().getArguments();
        // which variable have ``influence'' on t?
        UnionFind<TRSVariable> uf = new UnionFind<>();
        for (Constraint constraint : rule.getConstraints()) {
            constraint.getVariables();
            uf.union(constraint.getVariables());
        }
        ImmutableSet<ImmutableSet<TRSVariable>> partitions = uf.getPartitions();
        LinkedHashSet<TRSVariable> influence = new LinkedHashSet<>();
        Set<TRSVariable> tvars = t.getVariables();
        influence.addAll(tvars);
        for (ImmutableSet<TRSVariable> p : partitions) {
            for (TRSVariable v : tvars) {
                if (p.contains(v)) {
                    influence.addAll(p);
                    break;
                }
            }
        }
        // all arguments of the LHS that have ``influence'' on the value of t
        ArrayList<Integer> X = new ArrayList<>();
        for (int i = 0, l = lhsV.size(); i < l; ++i) {
            TRSVariable x = (TRSVariable) lhsV.get(i);
            if (!influence.contains(x)) {
                continue;
            }
            X.add(i);
        }
        return ImmutableCreator.create(X);
    }

}
