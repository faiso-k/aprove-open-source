package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.math.*;
import java.util.*;

import org.json.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;

/**
 * Store information about arithmetic operations working on integers/longs.
 * @author Christian von Essen
 */
public class IntegerResultInformation implements IntegerInformation {
    /**
     * Type of arithmetic operation performed.
     */
    private final ArithmeticOperationType arithmeticOperationType;

    /**
     * First abstract number used in this operation.
     */
    private final AbstractVariableReference firstNumber;

    /**
     * Second abstract number used in this operation.
     */
    private final AbstractVariableReference secondNumber;

    /**
     * Second number used in this operation.
     */
    private final LiteralInt secondConstant;

    /**
     * Result of this operation.
     */
    private final AbstractVariableReference resultNumber;

    /**
     * @param firstNum First abstract number used in this operation.
     * @param type Type of arithmetic operation performed.
     * @param secondNum Second abstract number used in this operation.
     * @param result Result of this operation.
     */
    public IntegerResultInformation(
            final AbstractVariableReference firstNum,
            final ArithmeticOperationType type,
            final AbstractVariableReference secondNum,
            final AbstractVariableReference result) {
        this.firstNumber = firstNum;
        this.secondNumber = secondNum;
        this.secondConstant = null;
        this.resultNumber = result;
        this.arithmeticOperationType = type;
    }

    /**
     * @param firstNum First abstract number used in this operation.
     * @param type Type of arithmetic operation performed.
     * @param constantArg Second abstract number used in this operation.
     * @param result Result of this operation.
     */
    public IntegerResultInformation(final AbstractVariableReference firstNum,
            final ArithmeticOperationType type, final LiteralInt constantArg,
            final AbstractVariableReference result) {
        this.firstNumber = firstNum;
        this.secondNumber = null;
        this.secondConstant = constantArg;
        this.resultNumber = result;
        this.arithmeticOperationType = type;
    }

    /**
     * @return String representation of this integer operation.
     */
    @Override
    public String toString() {
        final StringBuilder s = new StringBuilder();
        s.append(this.resultNumber).append("=");
        if (this.arithmeticOperationType == ArithmeticOperationType.NEG) {
            s.append(this.arithmeticOperationType.toString()).append(
                this.secondNumber);
        } else {
            s.append(this.firstNumber);
            s.append(this.arithmeticOperationType.toString());
            if (this.secondConstant == null) {
                s.append(this.secondNumber);
            } else {
                s.append(this.secondConstant);
            }
        }
        return s.toString();
    }

    /**
     * @return type of arithmetic operation performed.
     */
    public ArithmeticOperationType getArithmeticOperationType() {
        return this.arithmeticOperationType;
    }

    /**
     * @return result of this operation.
     */
    public AbstractVariableReference getResult() {
        return this.resultNumber;
    }

    /**
     * @return First abstract number used in this operation.
     */
    public AbstractVariableReference getFirstNumber() {
        return this.firstNumber;
    }

    /**
     * @return Second abstract number used in this operation.
     */
    public AbstractVariableReference getSecondNumber() {
        assert (this.secondConstant == null);
        return this.secondNumber;
    }

    /**
     * @return true iff the second argument is a constant
     */
    public boolean secondIsConstant() {
        return this.secondConstant != null;
    }

    /**
     * @return the constant value of the second argument
     */
    public AbstractInt getSecondConstant() {
        assert (this.secondConstant != null);
        return this.secondConstant;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime
                * result
                + ((this.arithmeticOperationType == null) ? 0
                    : this.arithmeticOperationType.hashCode());
        result =
            prime * result
                + ((this.firstNumber == null) ? 0 : this.firstNumber.hashCode());
        result =
            prime * result
                + ((this.resultNumber == null) ? 0 : this.resultNumber.hashCode());
        result =
            prime * result
                + ((this.secondConstant == null) ? 0 : this.secondConstant.hashCode());
        result =
            prime * result
                + ((this.secondNumber == null) ? 0 : this.secondNumber.hashCode());
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final IntegerResultInformation other = (IntegerResultInformation) obj;
        if (this.arithmeticOperationType == null) {
            if (other.arithmeticOperationType != null) {
                return false;
            }
        } else if (!this.arithmeticOperationType.equals(other.arithmeticOperationType)) {
            return false;
        }
        if (this.firstNumber == null) {
            if (other.firstNumber != null) {
                return false;
            }
        } else if (!this.firstNumber.equals(other.firstNumber)) {
            return false;
        }
        if (this.resultNumber == null) {
            if (other.resultNumber != null) {
                return false;
            }
        } else if (!this.resultNumber.equals(other.resultNumber)) {
            return false;
        }
        if (this.secondConstant == null) {
            if (other.secondConstant != null) {
                return false;
            }
        } else if (!this.secondConstant.equals(other.secondConstant)) {
            return false;
        }
        if (this.secondNumber == null) {
            if (other.secondNumber != null) {
                return false;
            }
        } else if (!this.secondNumber.equals(other.secondNumber)) {
            return false;
        }
        return true;
    }

    @Override
    public SMTLIBTheoryAtom toSMTAtom(final String varPrefix) {
        final SMTLIBIntValue result = this.resultNumber.toSMTIntValue(varPrefix);
        final SMTLIBIntValue firstOperand;
        if (this.firstNumber != null) {
            firstOperand = this.firstNumber.toSMTIntValue(varPrefix);
        } else {
            assert (this.arithmeticOperationType == ArithmeticOperationType.NEG)
                : "Only one operand, but binary int operation";
            firstOperand = SMTLIBIntConstant.create(BigInteger.valueOf(-1));
        }
        final SMTLIBIntValue secondOperand;
        if (this.secondConstant != null) {
            secondOperand = this.secondConstant.toSMTIntValue();
        } else {
            secondOperand = this.secondNumber.toSMTIntValue(varPrefix);
        }
        final List<SMTLIBIntValue> operands = new LinkedList<SMTLIBIntValue>();
        operands.add(firstOperand);
        operands.add(secondOperand);
        final SMTLIBIntArithFunc operation;
        switch (this.arithmeticOperationType) {
            case ADD:
                operation = SMTLIBIntPlus.create(operands);
                break;
            case SUB:
                operation = SMTLIBIntMinus.create(operands);
                break;
            case NEG:
            case MUL:
            // for NEG this is also correct, we do x * -1
                operation = SMTLIBIntMult.create(operands);
                break;
            case EIDIV:
                if (this.secondIsConstant() || this.secondNumber.pointsToConstantInt()) {
                    operation = SMTLIBIntDiv.create(operands);
                } else {
                    throw new UnsupportedOperationException();
                }
                break;
            case EMOD:
                if (this.secondIsConstant() || this.secondNumber.pointsToConstantInt()) {
                    operation = SMTLIBIntMod.create(operands);
                } else {
                    throw new UnsupportedOperationException();
                }
                break;
            default:
                throw new UnsupportedOperationException();
        }

        return SMTLIBIntEquals.create(result, operation);
    }

    /** {@inheritDoc} */
    @Override
    public boolean concernsInterestingRef(final Set<AbstractVariableReference>... interestingRefs) {
        for (final Set<AbstractVariableReference> refSet : interestingRefs) {
            if (refSet == null || refSet.contains(this.firstNumber) || refSet.contains(this.secondNumber)
                || refSet.contains(this.resultNumber)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Integer Arithmetic Result");
        res.put("Operation",   "(" + this.getArithmeticOperationType().toString()
                             + " " + this.getFirstNumber().toString()
                             + " " + this.getSecondNumber().toString()
                             + ")");
        return res;
    }
}
