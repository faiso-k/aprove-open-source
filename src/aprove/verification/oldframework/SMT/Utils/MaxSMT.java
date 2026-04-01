package aprove.verification.oldframework.SMT.Utils;

import java.math.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;

public class MaxSMT {

    private static final Logger log = Logger.getLogger(SExpProcessCommunicator.class.toString());

    public static BigInteger maximizeIntExpr(
        SMTSolver f,
        Abortion abortion,
        SMTExpression<SInt> expression,
        BigInteger lower,
        BigInteger upper)
    {
        if (MaxSMT.log.isLoggable(Level.FINE)) {
            MaxSMT.log.fine("MaxSMT: starting binary search, lower: " + lower + ", upper: " + upper);
        }
        abortion.checkAbortion();

        assert lower.compareTo(upper) <= 0;

        f.push();
        f.addAssertion(Ints.lessEqual(Ints.constant(lower), expression));
        f.addAssertion(Ints.lessEqual(expression, Ints.constant(upper)));

        if (!YNM.YES.equals(f.checkSAT())) {
            return null;
        }

        // we know that a solution exists in the range, now find the largest one
        BigInteger n = MaxSMT.realMaximizeInt(f, abortion, expression, lower, upper);
        f.pop();
        f.addAssertion(Ints.lessEqual(Ints.constant(n), expression));
        return n;
    }

    private static BigInteger realMaximizeInt(
        SMTSolver j,
        Abortion abortion,
        SMTExpression<SInt> expression,
        BigInteger lower,
        BigInteger upper)
    {
        if (MaxSMT.log.isLoggable(Level.FINE)) {
            MaxSMT.log.fine("MaxSMT: binary search step, lower: " + lower + ", upper: " + upper);
        }
        assert lower.compareTo(upper) <= 0;

        if (lower.equals(upper)) {
            return upper;
        }
        abortion.checkAbortion();

        BigInteger middle = lower.add(upper).divide(BigInteger.valueOf(2)).add(BigInteger.ONE);

        j.push();
        j.addAssertion(Ints.lessEqual(Ints.constant(middle), expression));
        YNM res = j.checkSAT();
        j.pop();
        switch (res) {
        case YES:
            return MaxSMT.realMaximizeInt(j, abortion, expression, middle, upper);
        case NO:
            return MaxSMT.realMaximizeInt(j, abortion, expression, lower, middle.subtract(BigInteger.ONE));
        case MAYBE:
        default:
            throw new RuntimeException("Strange SMT Solver.");
        }
    }

}
