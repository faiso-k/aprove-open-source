package aprove.input.Programs.prolog.graph;

import java.math.*;
import java.util.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;

public class PrologToIntegerConverter {

    public static PrologToIntegerConverter create() {
        return new PrologToIntegerConverter();
    }

    /**
     * A term may be equivalent to no relation if it, for example, contains predicate symbols that
     * do not correspond to any arithmetic operation or it contains NonAbstractVars.
     * @param t Some term.
     * @return A relation equivalent to the given term. Null if the given term is equivalent to no relation.
     */
    public IntegerRelation convertRelation(PrologTerm t) {
        return this.convertToRelation(t);
    }

    /**
     * In order to apply a prolog substitution to an arithmetic state, we need
     * to talk about LLVMReferences instead of PrologVariables. This method
     * performs the translation from Prolog to LLVM in a straightforward way. If
     * some variable is substituted by something that is not an arithmetic
     * expression, then that substitution is not included in the result.
     *
     * @param prologSubstitution
     *            Some substitution
     * @return The same substitution in LLVM-terms
     */
    public Map<IntegerVariable, FunctionalIntegerExpression> convertSubstitution(
        PrologSubstitution prologSubstitution
    ) {
        final Map<IntegerVariable, FunctionalIntegerExpression> returnValue =
            new HashMap<IntegerVariable, FunctionalIntegerExpression>();
        for (Map.Entry<PrologVariable, PrologTerm> prologEntry : prologSubstitution.entrySet()) {
            final FunctionalIntegerExpression variable = this.convertToExpression(prologEntry.getKey());
            assert variable instanceof IntegerVariable;
            final FunctionalIntegerExpression replacement = this.convertToExpression(prologEntry.getValue());
            if (replacement != null) {
                returnValue.put((IntegerVariable)variable, replacement);
            }
        }
        return returnValue;
    }

    private FunctionalIntegerExpression convertToExpression(PrologTerm t) {
        if (t.isInt()) {
            return new PlainIntegerConstant(((PrologInt)t).getValue());
        } else if (t.isVariable()) {
            return new PlainIntegerVariable(((PrologVariable)t).getName());
        }
        final FunctionSymbol prologOperatorFunctionSymbol = t.createFunctionSymbol();
        if (!PrologBuiltins.ARITHMETIC_OPERATORS.contains(prologOperatorFunctionSymbol)) {
            return null;
        }
        if (t.getArity() == 1) {
            assert (prologOperatorFunctionSymbol.getName().equals(PrologBuiltin.MINUS_NAME)) :
                "Unary arithmetic operator that is not -";
            final FunctionalIntegerExpression arg = this.convertToExpression(t.getArgument(0));
            assert arg != null;
            return
                new PlainIntegerOperation(
                    ArithmeticOperationType.MUL,
                    new PlainIntegerConstant(BigInteger.valueOf(-1)),
                    arg
                );
        }
        assert t.getArity() == 2 : "Non-binary operator";
        final ArithmeticOperationType op;
        switch (prologOperatorFunctionSymbol.getName()) {
            case PrologBuiltin.PLUS_NAME:
                op = ArithmeticOperationType.ADD;
                break;
            case PrologBuiltin.MINUS_NAME:
                op = ArithmeticOperationType.SUB;
                break;
            case PrologBuiltin.TIMES_NAME:
                op = ArithmeticOperationType.MUL;
                break;
            case PrologBuiltin.DIV_NAME:
                op = ArithmeticOperationType.MDIV;
                break;
            case PrologBuiltin.INTDIV_NAME:
                op = ArithmeticOperationType.TIDIV;
                break;
            case PrologBuiltin.MODULO_NAME:
                op = ArithmeticOperationType.EMOD;
                break;
            case PrologBuiltin.INTPOWER_NAME:
                op = ArithmeticOperationType.POW;
                break;
            default:
                throw new UnsupportedOperationException("We do not need this right now, will implement it later");
        }
        final FunctionalIntegerExpression lhs = this.convertToExpression(t.getArgument(0));
        final FunctionalIntegerExpression rhs = this.convertToExpression(t.getArgument(1));
        if (lhs == null || rhs == null) {
            return null;
        } else {
            return new PlainIntegerOperation(op, lhs, rhs);
        }
    }

    private IntegerRelation convertToRelation(PrologTerm t) {
        final FunctionSymbol prologRelationSymbol = t.createFunctionSymbol();
        if (!PrologBuiltins.ARITHMETIC_COMPARISON_PREDICATES.contains(prologRelationSymbol)) {
            return null;
        }
        assert t.getArity() == 2 : "Relation without two arguments";
        final FunctionalIntegerExpression firstArg = this.convertToExpression(t.getArgument(0));
        if (firstArg == null) {
            return null;
        }
        final FunctionalIntegerExpression secondArg = this.convertToExpression(t.getArgument(1));
        if (secondArg == null) {
            return null;
        }
        final IntegerRelationType relationType;
        final FunctionalIntegerExpression lhs, rhs;
        switch (prologRelationSymbol.getName()) {
            case PrologBuiltin.LESS_NAME:
                relationType = IntegerRelationType.LT;
                lhs = firstArg;
                rhs = secondArg;
                break;
            case PrologBuiltin.LEQ_NAME:
                relationType = IntegerRelationType.LE;
                lhs = firstArg;
                rhs = secondArg;
                break;
            case PrologBuiltin.ISEQUAL_NAME:
                relationType = IntegerRelationType.EQ;
                lhs = firstArg;
                rhs = secondArg;
                break;
            case PrologBuiltin.ISUNEQUAL_NAME:
                relationType = IntegerRelationType.NE;
                lhs = firstArg;
                rhs = secondArg;
                break;
            case PrologBuiltin.GREATER_NAME:
                relationType = IntegerRelationType.LT;
                lhs = secondArg;
                rhs = firstArg;
                break;
            case PrologBuiltin.GEQ_NAME:
                relationType = IntegerRelationType.LE;
                lhs = secondArg;
                rhs = firstArg;
                break;
            default:
                assert false : "Apparently PrologBuiltins.ARITHMETIC_COMPARISON_OPERATORS does not contain all of them";
                return null;
        }
        return new PlainIntegerRelation(relationType, lhs, rhs);
    }

}
