package aprove.verification.oldframework.BasicStructures;

import java.util.*;

import org.json.*;

/**
 * A variable is just a name.
 * @author cryingshadow
 * @version $Id$
 */
public interface Variable extends SimpleExpression {

    /**
     * @param v Some non-null variable.
     * @param o Some object.
     * @return True iff the specified arguments are equal.
     */
    public static boolean equals(Variable v, Object o) {
        if (o == null) {
            return false;
        }
        if (v == o) {
            return true;
        }
        if (!v.getClass().equals(o.getClass())) {
            return false;
        }
        return v.getName().equals(((Variable)o).getName());
    }

    /**
     * @param v Some variable.
     * @return The set of variables occurring in v (i.e., the singleton set {v}).
     */
    public static Set<? extends Variable> getVariables(Variable v) {
        return Collections.singleton(v);
    }

    /**
     * @param v Some non-null variable.
     * @return A hash code for the specified variable.
     */
    public static int hashCode(Variable v) {
        return v.getClass().hashCode() + v.getName().hashCode();
    }

    /**
     * @param v Some variable.
     * @return A JSONObject representing the specified variable.
     */
    public static JSONObject toJSON(Variable v) {
        JSONObject res = new JSONObject();
        res.put("type", v.getClass().getSimpleName());
        res.put("name", v.getName());
        return res;
    }

    @Override
    default Expression applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        if (sigma.containsKey(this)) {
            return sigma.get(this);
        }
        return this;
    }

    @Override
    default Expression applySubstitution(Substitution sigma) {
        return sigma.substitute(this);
    }

    @Override
    default Set<? extends Variable> getVariables() {
        return Variable.getVariables(this);
    }

    @Override
    default Object toJSON() {
        return Variable.toJSON(this);
    }

    @Override
    default String toSExpressionString() {
        return "( var " + this.getName() + " )";
    }

}
