package aprove.verification.oldframework.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * An expression is either a compound expression or a constant expression.
 * @author cryingshadow
 * @version $Id$
 */
public interface Expression
extends
    Immutable,
    Exportable,
    HasVariables,
    HasName,
    DOTStringAble,
    Visitable<Expression, Expression>,
    SStringExpressible,
    Substitutable,
    JSONExport
{

    /**
     * @param orig The original expression.
     * @param v The variable.
     * @param e The expression by which the variable should be replaced.
     * @return The original expression where every occurrence of the specified variable has been replaced by the
     *         specified expression simultaneously.
     */
    @SuppressWarnings("unchecked")
    public static <E extends Expression, V extends Variable, F extends Expression> E applySubstitution(
        E orig,
        V v,
        F e
    ) {
        return (E)orig.applySubstitution(Substitution.toSubstitution(Collections.<V, F>singletonMap(v, e)));
    }

    @Override
    default Expression applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    Expression applySubstitution(Substitution sigma);

    @Override
    default Expression applySubstitution(Variable v, Expression e) {
        return Expression.applySubstitution(this, v, e);
    }

    @Override
    default String export(Export_Util eu) {
        return eu.export(this.toPrettyString());
    }

    @Override
    default String toDOTString() {
        // substitute double quote signs in the String representation with single quote signs (double quotes causes
        // problems in the dot file)
        return this.toPrettyString().replace('"', '\'');
    }

    /**
     * @return A human-readable String representation of this.
     */
    String toPrettyString();

}
