package aprove.input.Programs.prolog.graph;

import java.math.*;
import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Logic.*;

class SafeEvaluationHeuristic {

    public static SafeEvaluationHeuristic create(PrologToIntegerConverter converter) {
        return new SafeEvaluationHeuristic(converter);
    }

    private final PrologToIntegerConverter converter;

    private SafeEvaluationHeuristic(PrologToIntegerConverter converter) {
        this.converter = converter;
    }

    public YNM isSafe(
        Set<PrologAbstractVariable> groundExpressionVars,
        IntegerState arithmeticState,
        PrologTerm t,
        Abortion aborter
    ) {
        if (t.isInt()) {
            return YNM.YES;
        } else if (t.isNumber()) {
            // Since t is a number, but not an integer, it must be a float, which we cannot handle right now
            return YNM.NO;
        } else if (t.isNonAbstractVariable()) {
            return YNM.NO;
        } else if (t.isAbstractVariable()) {
            return (groundExpressionVars.contains(t) ? YNM.YES : YNM.MAYBE);
        }
        final FunctionSymbol termFunctionSymbol = t.createFunctionSymbol();
        if (!PrologBuiltins.ARITHMETIC_OPERATORS.contains(termFunctionSymbol)) {
            return YNM.NO;
        }
        assert t.getArity() == 2 : "Non-binary arithmetic operator";
        final YNM lhsSafe = this.isSafe(groundExpressionVars, arithmeticState, t.getArgument(0), aborter);
        final YNM rhsSafe = this.isSafe(groundExpressionVars, arithmeticState, t.getArgument(1), aborter);
        if (termFunctionSymbol.equals(PrologBuiltin.DIV_SYMBOL)) {
            if (lhsSafe == YNM.MAYBE || rhsSafe == YNM.MAYBE) {
                return YNM.MAYBE;
            } else if (lhsSafe == YNM.NO || rhsSafe == YNM.NO) {
                return YNM.NO;
            } else {
                // lhsSafe == rhsSafe == YNM.YES
                final PrologTerm rhsNeqZeroTerm =
                    PrologTerm.create(PrologBuiltin.ISUNEQUAL_NAME, t.getArgument(1), new PrologInt(BigInteger.ZERO));
                final IntegerRelation rhsNeqZeroRel = this.converter.convertRelation(rhsNeqZeroTerm);
                if (arithmeticState.checkRelation(rhsNeqZeroRel, aborter).x) {
                    return YNM.YES;
                }
                if (arithmeticState.checkRelation(rhsNeqZeroRel.negate(), aborter).x) {
                    return YNM.NO;
                }
                return YNM.MAYBE;
            }
        } else {
            if (lhsSafe == YNM.MAYBE || rhsSafe == YNM.MAYBE) {
                return YNM.MAYBE;
            } else if (lhsSafe == YNM.NO || rhsSafe == YNM.NO) {
                return YNM.NO;
            } else {
                return YNM.YES;
            }
        }
    }

}
