package aprove.verification.oldframework.BasicStructures;

import java.util.*;


/**
 * A constant which is no variable.
 * @author cryingshadow
 * @version $Id$
 */
public interface ConstantExpression extends SimpleExpression {

    /**
     * @param c Some constant.
     * @return The set of variables occurring in c (i.e., the empty set).
     */
    public static Set<? extends Variable> getVariables(ConstantExpression c) {
        return Collections.emptySet();
    }

    @Override
    default ConstantExpression applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this;
    }

    @Override
    default ConstantExpression applySubstitution(Substitution sigma) {
        return this;
    }

    @Override
    default Set<? extends Variable> getVariables() {
        return ConstantExpression.getVariables(this);
    }

    @Override
    default String toSExpressionString() {
        return this.getName();
    }

}
