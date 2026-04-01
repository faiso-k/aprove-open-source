package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.math.*;
import java.util.*;

import org.json.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;

/**
 * An integer.
 * @author cryingshadow
 * @version $Id$
 */
public interface IntegerConstant extends IntegerFunctionExpression, ConstantExpression {

    /**
     * @param c Some non-null constant.
     * @param o Some object.
     * @return True iff the specified arguments are equal.
     */
    public static boolean equals(IntegerConstant c, Object o) {
        if (o == null) {
            return false;
        }
        if (c == o) {
            return true;
        }
        if (!c.getClass().equals(o.getClass())) {
            return false;
        }
        return c.getIntegerValue().compareTo(((IntegerConstant)o).getIntegerValue()) == 0;
    }

    /**
     * @param c Some non-null constant.
     * @return A hash code for the specified constant consistent with the static equals method in this class.
     */
    public static int hashCode(IntegerConstant c) {
        return c.getClass().hashCode() + c.getIntegerValue().hashCode();
    }

    /**
     * @return The value of this constant.
     */
    BigInteger getIntegerValue();

    @Override
    default String getName() {
        return this.getIntegerValue().toString();
    }

    @Override
    default FunctionSymbol getRootSymbol() {
        return FunctionSymbol.create(this.getIntegerValue().toString(), 0);
    }

    @Override
    @SuppressWarnings("unchecked")
    default Set<? extends IntegerVariable> getVariables() {
        return (Set<? extends IntegerVariable>)ConstantExpression.getVariables(this);
    }

    @Override
    default Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("value", this.getIntegerValue().toString());
        return res;
    }

    @Override
    default String toPrettyString() {
        BigInteger value = this.getIntegerValue();
        return value.compareTo(BigInteger.ZERO) < 0 ? "(" + value.toString() + ")" : value.toString();
    }

    @Override
    default SMTExpression<SInt> toSMTExp() {
        return Ints.constant(this.getIntegerValue());
    }

}
