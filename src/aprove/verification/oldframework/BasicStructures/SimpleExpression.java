package aprove.verification.oldframework.BasicStructures;

import aprove.prooftree.Export.Utility.*;

/**
 * A simple expression has no sub-expressions.
 * @author cryingshadow
 * @version $Id$
 */
public interface SimpleExpression extends Expression {

    @Override
    default Expression accept(Visitor<Expression, Expression> v) {
        return v.visit(this);
    }

    @Override
    default String toPrettyString() {
        return this.getName();
    }

    @Override
    default String export(Export_Util eu) {
        return eu.export(this.getName());
    }

}
