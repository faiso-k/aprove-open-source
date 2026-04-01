package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * Represents a binary operation like add, and, subtract, multiply, ...
 * @author Janine Repke, Marc Brockschmidt, cryingshadow
 */
public class LLVMOperation implements LLVMFunctionApplication, BinaryIntegerFunctionExpression {

    /**
     * Left-hand side of this (binary) operation. Never null.
     */
    private final LLVMTerm lhs;

    /**
     * Type of the (binary) operation. Never null.
     */
    private final ArithmeticOperationType opType;

    /**
     * Right-hand side of this (binary) operation. Never null.
     */
    private final LLVMTerm rhs;

    /**
     * Creates an operation. Should not be used outside of factory methods (this is why it is package private).
     * @param op Type of the (binary) operation. May never be null.
     * @param l Left-hand side of this (binary) operation. May never be null.
     * @param r Right-hand side of this (binary) operation. May never be null.
     */
    LLVMOperation(ArithmeticOperationType op, LLVMTerm l, LLVMTerm r) {
        if (Globals.useAssertions) {
            assert (op != null) : "OperationType must not be null!";
            assert (l != null && r != null) : "Arguments must not be null!";
        }
        this.lhs = l;
        this.rhs = r;
        this.opType = op;
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof LLVMOperation) {
            LLVMOperation other = (LLVMOperation)o;
            if (this.opType != other.opType) {
                return false;
            }
            // note that both sides must be non-null
            return this.lhs.equals(other.lhs) && this.rhs.equals(other.rhs);
        } else {
            return false;
        }
    }

    @Override
    public LLVMConstant evaluate(LLVMTermFactory factory) throws DivisionByZeroException {
        LLVMConstant left = this.getLhs().evaluate(factory);
        if (left == null) {
            return null;
        }
        LLVMConstant right = this.getRhs().evaluate(factory);
        if (right == null) {
            return null;
        }
        final BigInteger res;
        try {
            res = this.getOperation().evaluateOnIntegers(left.getIntegerValue(), right.getIntegerValue());
        } catch (UnsupportedOperationException e) {
            return null;
        }
        return factory.constant(res);
    }

    @Override
    public LLVMTerm getLhs() {
        return this.lhs;
    }

    @Override
    public ArithmeticOperationType getOperation() {
        return this.opType;
    }

    @Override
    public LLVMTerm getRhs() {
        return this.rhs;
    }

    @Override
    @SuppressWarnings("unchecked")
    public Set<? extends LLVMSymbolicVariable> getVariables() {
        return (Set<? extends LLVMSymbolicVariable>)CompoundExpression.getVariables(this);
    }

    @Override
    public int hashCode() {
        int prime = 31;
        int result = 1;
        result = prime * result + this.getLhs().hashCode() + this.getRhs().hashCode();
        result = prime * result + this.getOperation().ordinal();
        return result;
    }

    @Override
    public LLVMTerm negate() {
        return LLVMTerm.negate(this, this.getTermFactory());
    }

    @Override
    public LLVMOperation setLhs(Expression lhs) {
        return this.setLhs((LLVMTerm)lhs);
    }

    /**
     * @param lhsParam The new left-hand side.
     * @return An LLVMFunctionApplication with the specified left-hand side and the current right-hand side.
     */
    public LLVMOperation setLhs(LLVMTerm lhsParam) {
        return new LLVMOperation(this.getOperation(), lhsParam, this.getRhs());
    }

    @Override
    public LLVMOperation setRhs(Expression rhs) {
        return this.setRhs((LLVMTerm)rhs);
    }

//    @Override
//    public SMTLIBIntValue toSMTIntValue() {
//        List<SMTLIBIntValue> operands = new LinkedList<SMTLIBIntValue>();
//        operands.add(this.getLhs().toSMTIntValue());
//        operands.add(this.getRhs().toSMTIntValue());
//        switch (this.getOperation()) {
//        case ADD:
//            return SMTLIBIntPlus.create(operands);
//        case SUB:
//            return SMTLIBIntMinus.create(operands);
//        case MUL:
//            return SMTLIBIntMult.create(operands);
//        case DIV:
//            return SMTLIBIntDiv.create(operands);
//        default:
//            throw new UnsupportedOperationException("No viable cases left. Operation: " + this.getOperation());
//        }
//    }

    /**
     * @param rhsParam The new right-hand side.
     * @return A LLVMFunctionApplication with the current left-hand side and the specified right-hand side.
     */
    public LLVMOperation setRhs(LLVMTerm rhsParam) {
        return new LLVMOperation(this.getOperation(), this.getLhs(), rhsParam);
    }

    @Override
    public String toString() {
        return this.toPrettyString();
    }

    @Override
    public TRSTerm toTerm() {
        TRSTerm lhsTerm = this.getLhs().toTerm();
        TRSTerm rhsTerm = this.getRhs().toTerm();
        FunctionSymbol functionSymbol;
        switch (this.getOperation()) {
            case ADD:
                functionSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Add, DomainFactory.INTEGER_INTEGER);
                break;
            case TIDIV:
                functionSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Div, DomainFactory.INTEGER_INTEGER);
                break;
            case TMOD:
                /*
                 * As Func.Mod has not the correct semantics (we need sign of dividend whereas mod computes sign of
                 * divisor), we need a more sophisticated encoding here (note that it computes the sign correctly):
                 * l % r = l - ((l / r) * r)
                 */
                return
                    TRSTerm.createFunctionApplication(
                        IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Sub, DomainFactory.INTEGER_INTEGER),
                        lhsTerm,
                        TRSTerm.createFunctionApplication(
                            IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Mul, DomainFactory.INTEGER_INTEGER),
                            TRSTerm.createFunctionApplication(
                                IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Div, DomainFactory.INTEGER_INTEGER),
                                lhsTerm,
                                rhsTerm
                            ),
                            rhsTerm
                        )
                    );
            case EMOD:
                functionSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Mod, DomainFactory.INTEGER_INTEGER);
                break;
            case MUL:
                functionSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Mul, DomainFactory.INTEGER_INTEGER);
                break;
            case SUB:
                functionSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Sub, DomainFactory.INTEGER_INTEGER);
                break;
            case AND:
                if (Globals.useAssertions) {
                    assert (this.lhs instanceof LLVMConstant) : "Left-hand side of AND is not constant!";
                    BigInteger leftVal = ((LLVMConstant)this.lhs).getIntegerValue();
                    assert (leftVal.compareTo(BigInteger.ZERO) >= 0) : "Left-hand side of AND is negative!";
                    assert (leftVal.compareTo(BigInteger.ONE) <= 0) : "Left-hand side of AND is no boolean!";
                    assert (this.rhs instanceof LLVMConstant) : "Right-hand side of AND is not constant!";
                    BigInteger rightVal = ((LLVMConstant)this.lhs).getIntegerValue();
                    assert (rightVal.compareTo(BigInteger.ZERO) >= 0) : "Right-hand side of AND is negative!";
                    assert (rightVal.compareTo(BigInteger.ONE) <= 0) : "Right-hand side of AND is no boolean!";
                }
                functionSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Land, DomainFactory.BOOLEAN_BOOLEAN);
                break;
            case OR:
                if (Globals.useAssertions) {
                    assert (this.lhs instanceof LLVMConstant) : "Left-hand side of OR is not constant!";
                    BigInteger leftVal = ((LLVMConstant)this.lhs).getIntegerValue();
                    assert (leftVal.compareTo(BigInteger.ZERO) >= 0) : "Left-hand side of OR is negative!";
                    assert (leftVal.compareTo(BigInteger.ONE) <= 0) : "Left-hand side of OR is no boolean!";
                    assert (this.rhs instanceof LLVMConstant) : "Right-hand side of OR is not constant!";
                    BigInteger rightVal = ((LLVMConstant)this.lhs).getIntegerValue();
                    assert (rightVal.compareTo(BigInteger.ZERO) >= 0) : "Right-hand side of OR is negative!";
                    assert (rightVal.compareTo(BigInteger.ONE) <= 0) : "Right-hand side of OR is no boolean!";
                }
                functionSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Lor, DomainFactory.BOOLEAN_BOOLEAN);
                break;
                //        case XOR:
                //            if (Globals.useAssertions) {
                //                assert (this.lhs instanceof LLVMConstant) : "Left-hand side of XOR is not constant!";
                //                BigInteger leftVal = ((LLVMConstant)this.lhs).getValue();
                //                assert (leftVal.compareTo(BigInteger.ZERO) >= 0) : "Left-hand side of XOR is negative!";
                //                assert (leftVal.compareTo(BigInteger.ONE) <= 0) : "Left-hand side of XOR is no boolean!";
                //                assert (this.rhs instanceof LLVMConstant) : "Right-hand side of XOR is not constant!";
                //                BigInteger rightVal = ((LLVMConstant)this.lhs).getValue();
                //                assert (rightVal.compareTo(BigInteger.ZERO) >= 0) : "Right-hand side of XOR is negative!";
                //                assert (rightVal.compareTo(BigInteger.ONE) <= 0) : "Right-hand side of XOR is no boolean!";
                //            }
                //            // TODO check whether this predefined symbol is correct
                //            functionSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Bwxor, DomainFactory.BOOLEAN_BOOLEAN);
                //            break;
            default:
                throw new UnsupportedOperationException(
                    "There are no viable cases left. Case optype: " + this.getOperation().name()
                );
        }
        return TRSTerm.createFunctionApplication(functionSymbol, lhsTerm, rhsTerm);
    }

}
