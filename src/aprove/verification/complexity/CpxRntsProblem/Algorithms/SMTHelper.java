package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.io.IOException;
import java.math.BigInteger;
import java.util.LinkedHashSet;
import java.util.Set;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.Z3.*;
import aprove.verification.oldframework.SMT.Utils.*;

public abstract class SMTHelper {

    /**
     * @return true if guard is unsatisfiable. false is not meaningful.
     * @note guard must only contain polynomial expressions
     */
    public static boolean isUnsat(Set<Constraint> guard, int timeout, Abortion aborter) {
        Set<SimplePolynomial> pols = new LinkedHashSet<>();
        for (Constraint c : guard) {
            try {
                pols.addAll(c.computePolynomials());
            } catch (NotRepresentableAsPolynomialsException e) {
                throw new RuntimeException(e);
            }
        }

        VariableScope scope = new VariableScope();
        SMTSolver solver = new Z3IntSolver(SMTLIBLogic.QF_NIA,timeout,aborter);
        for (SimplePolynomial pol : pols) {
            solver.addAssertion(Ints.greaterEqual(pol.toSMT(scope), new IntConstant(BigInteger.ZERO)));
        }

        boolean result = solver.checkSAT().equals(YNM.NO);
        try {
            solver.dispose();
        } catch (IOException e) {
            //ignore
        }
        return result;
    }
}
