package aprove.verification.oldframework.BasicStructures;

import java.util.*;

import immutables.*;

/**
 * A substitution replaces variables by expressions.
 * @author unknown, cryingshadow
 * @version $Id$
 */
public interface Substitution {

    /**
     * @param compound The compound expression to apply the substitution to.
     * @param sigma The substitution.
     * @return The result of applying sigma to compound.
     */
    @SuppressWarnings("unchecked")
    public static <C extends CompoundExpression, S extends Substitution> C applySubstitution(C compound, S sigma) {
        ArrayList<Expression> newArgs = new ArrayList<Expression>();
        for (Expression arg : compound.getArguments()) {
            newArgs.add(arg.applySubstitution(sigma));
        }
        return (C)compound.setArguments(ImmutableCreator.create(newArgs));
    }

    /**
     * @param sigma Some substitution as map.
     * @return The corresponding Substitution.
     */
    public static Substitution toSubstitution(final Map<? extends Variable, ? extends Expression> sigma) {
        return
            new Substitution() {

                @Override
                public Expression substitute(Variable v) {
                    if (sigma.containsKey(v)) {
                        return sigma.get(v);
                    }
                    return v;
                }

            };
    }

    /**
     * @param v Some Variable.
     * @return The Term to substitute the specified Variable.
     */
    Expression substitute(Variable v);

}
