package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import org.json.*;

import aprove.verification.oldframework.Bytecode.OpCodes.FloatArithmetic.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Store information about arithmetic operations working on floats/doubles.
 * @author Carsten Otto
 */
public class FloatResultInformation implements FloatInformation {
    /**
     * Type of arithmetic operation performed.
     */
    private final FloatArithType arithmeticOperationType;

    /**
     * First abstract number used in this operation.
     */
    private final AbstractVariableReference firstNumber;

    /**
     * Second abstract number used in this operation.
     */
    private final AbstractVariableReference secondNumber;

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
    public FloatResultInformation(
            final AbstractVariableReference firstNum,
            final FloatArithType type,
            final AbstractVariableReference secondNum,
            final AbstractVariableReference result) {
        this.firstNumber = firstNum;
        this.secondNumber = secondNum;
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
        if (this.arithmeticOperationType == FloatArithType.NEG) {
            s.append(this.arithmeticOperationType.toString()).append(
                this.secondNumber);
        } else {
            s.append(this.firstNumber);
            s.append(this.arithmeticOperationType.toString());
            s.append(this.secondNumber);
        }
        return s.toString();
    }

    /**
     * @return type of arithmetic operation performed.
     */
    public FloatArithType getArithmeticOperationType() {
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
        return this.secondNumber;
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
        final FloatResultInformation other = (FloatResultInformation) obj;
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
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Float Arithmetic Result");
        res.put("Operation",   "(" + this.getArithmeticOperationType().toString()
                             + " " + this.getFirstNumber().toString()
                             + " " + this.getSecondNumber().toString()
                             + ")");
        return res;
    }
}
