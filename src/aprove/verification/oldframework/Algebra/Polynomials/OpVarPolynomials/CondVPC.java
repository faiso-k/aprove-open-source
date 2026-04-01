package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * For those valuations for which the conjunction over all the
 * conditions in this.conditions holds, also this.constraint needs
 * to hold.
 *
 * @author fuhs
 * @version $Id$
 */
public class CondVPC {

    private VarPolyConstraint constraint;
    private List<CondVarPolynomial> conditions;

    /**
     * @param conditions
     * @param constraint
     */
    public CondVPC(List<CondVarPolynomial> conditions, VarPolyConstraint constraint) {
        this.constraint = constraint;
        this.conditions = conditions;
    }

    /**
     * @param x - a variable
     * @return this with its polynomial derived with respect to x;
     *  the conditions are the same as those of this
     */
    public CondVPC deriveWRT(String x) {
        VarPolyConstraint newVPC = this.constraint.deriveWRT(x);
        return new CondVPC(this.conditions, newVPC);
    }

    /**
     * Convenience method.
     * @param cs - constraints
     * @param x - a variable
     * @param allowValidRHSs - if some derivative contains an obviously
     *  valid rhs, put it into result?
     * @return cs with their rhs polynomials derived with respect to x;
     *  the conditions are the same as those of this
     */
    public static Set<CondVPC> deriveAllWRT(Collection<CondVPC> cs, String x,
            boolean allowValidRHSs) {
        Set<CondVPC> res = new LinkedHashSet<CondVPC>();
        for (CondVPC c : cs) {
            CondVPC cDer = c.deriveWRT(x);
            if (allowValidRHSs || ! cDer.constraint.isValid()) {
                res.add(cDer);
            }
        }
        return res;
    }

    /**
     * @return a representation of this in which the conditions are represented
     *  more directly:
     *  - x: the conditions
     *  - y: the constraint
     */
    public Pair<Set<VarPolyConstraint>, VarPolyConstraint> getFlattened() {
        Set<VarPolyConstraint> conds = new LinkedHashSet<VarPolyConstraint>();
        this.collectVPConditions(conds);
        return new Pair<Set<VarPolyConstraint>, VarPolyConstraint>(conds,
                this.constraint);
    }

    /**
     * Adds all conditions to vpConds that must be fulfilled for
     * this.constraint to have to hold.
     *
     * @param vpConds - non-null; is modified by this method
     */
    void collectVPConditions(Collection<VarPolyConstraint> vpConds) {
        for (CondVarPolynomial condVarPoly : this.conditions) {
            condVarPoly.collectVPConditions(vpConds);
        }
    }

    /**
     * The returned list is not meant to be modified!
     *
     * @return Returns the conditions.
     */
    public List<CondVarPolynomial> getConditions() {
        return this.conditions;
    }

    /**
     * @return Returns the constraint.
     */
    public VarPolyConstraint getConstraint() {
        return this.constraint;
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        boolean first = true;
        for (CondVarPolynomial condVP : this.conditions) {
            if (first) {
                first = false;
            }
            else if (condVP.hasConditions()) {
                b.append(" and ");
            }
            b.append(condVP.condsToString());
        }
        b.append("  ==>  ");
        b.append(this.constraint);
        b.append(" ");
        return b.toString();
    }
}
