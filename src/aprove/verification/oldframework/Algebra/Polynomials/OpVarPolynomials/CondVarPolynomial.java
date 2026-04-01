package aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * A CondVarPolynomial is a polynomial that takes its value poly only
 * for those instantiations by natural numbers for which the several
 * additional constraints (conditions) hold.
 *
 * @author fuhs
 * @version $Id$
 */
public class CondVarPolynomial {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.OpVarPolynomials.CondVarPolynomial");

    // Keep the constraints that stem from the *arguments* of some operator
    // in the non-conditional OpVP version of this separately. These are
    // accessible most easily via the corresponding CondVPs. For instance,
    // for max(p, q) + max(r, s), we need the CondVPs that correspond to
    // p, q, r, and s, respectively.
    private List<CondVarPolynomial> argumentConditions;

    // this condition must be fulfilled in addition to those from argumentConditions
    // for the value to be poly; null means that there is no additional condition.
    private VarPolyConstraint condition;

    // this is what we get when the conditions are fulfilled
    private VarPolynomial poly;


    /**
     * @param argumentConditions - the encapsulated conditions have to hold for
     *  this to take the value poly (non-null)
     * @param condition - additional condition for this (may be null)
     * @param poly
     */
    public CondVarPolynomial(List<CondVarPolynomial> argumentConditions,
            VarPolyConstraint condition, VarPolynomial poly) {
        this.argumentConditions = argumentConditions;
        this.condition = condition;
        this.poly = poly;
    }

    /**
     * Builds a CondVarPolynomial of the form
     *   TRUE => poly
     * (equivalent to poly itself)
     *
     * @param poly - to be encapsulated
     */
    public CondVarPolynomial(VarPolynomial poly) {
        this.argumentConditions = Collections.emptyList();
        this.condition = null;
        this.poly = poly;
    }


    /**
     * Collect all VPConditions required for this.
     *
     * @param vpConds - Used for collecting the conditions. Must not be null.
     */
    void collectVPConditions(Collection<VarPolyConstraint> vpConds) {
        for (CondVarPolynomial cvp : this.argumentConditions) {
            cvp.collectVPConditions(vpConds);
        }
        if (this.condition != null) {
            vpConds.add(this.condition);
        }
    }

    /**
     * @return Returns the argumentConditions.
     *  Modify only if you know what you are doing.
     */
    public List<CondVarPolynomial> getArgumentConditions() {
        return this.argumentConditions;
    }

    /**
     * @return Returns the condition.
     *  null means that there is no additional condition.
     */
    public VarPolyConstraint getCondition() {
        return this.condition;
    }

    /**
     * @return Returns the poly.
     */
    public VarPolynomial getPoly() {
        return this.poly;
    }

    /**
     * Tries to find inconsistencies between the constraints of this and
     * those of that. Does not check whether the atomic constraints as such
     * are satisfiable, but only if the combination of two constraints is.
     *
     * @param that
     * @return true if the conditions of this and that definitely cannot
     *  be satisfied at the same time; false if we do not know
     */
    public boolean checkCondsForInconsistency(CondVarPolynomial that) {
        LinkedHashSet<VarPolyConstraint> condsThis, condsThat;
        condsThis = new LinkedHashSet<VarPolyConstraint>();
        condsThat = new LinkedHashSet<VarPolyConstraint>();
        this.collectVPConditions(condsThis);
        that.collectVPConditions(condsThat);
        for (VarPolyConstraint cThis : condsThis) {
            if (cThis.getType() == ConstraintType.GE) {
                // so far, we only work on type GE
                for (VarPolyConstraint cThat : condsThat) {
                    if (cThat.getType() == ConstraintType.GE) {
                        VarPolynomial sum = cThis.getPolynomial().plus(cThat.getPolynomial());
                        VarPolyConstraint sumGEZero = new VarPolyConstraint(sum,
                                ConstraintType.GE);
                        if (sumGEZero.isUnsatisfiable()) {
                            if (Globals.DEBUG_FUHS && CondVarPolynomial.log.isLoggable(Level.FINEST)) {
                                CondVarPolynomial.log.finest(sumGEZero + " cannot hold: Conditions " +
                                        cThis + " and " + cThat +
                                        " inconsistent => omitting\n");
                            }
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    /**
     * Tries to find inconsistencies between the constraints of this and
     * vpc. Does not check whether the atomic constraints as such
     * are satisfiable, but only if the combination of two constraints is.
     *
     * @param vpc
     * @return true if the conditions of this and vpc definitely cannot
     *  be satisfied at the same time; false if we do not know
     */
    public boolean checkCondForInconsistency(VarPolyConstraint vpc) {
        if (vpc.getType() == ConstraintType.GE) {
            VarPolynomial vp = vpc.getPolynomial();
            LinkedHashSet<VarPolyConstraint> condsThis;
            condsThis = new LinkedHashSet<VarPolyConstraint>();
            this.collectVPConditions(condsThis);
            for (VarPolyConstraint cThis : condsThis) {
                if (cThis.getType() == ConstraintType.GE) {
                    // so far, we only work on type GE
                    VarPolynomial sum = cThis.getPolynomial().plus(vp);
                    VarPolyConstraint sumGEZero = new VarPolyConstraint(sum,
                            ConstraintType.GE);
                    if (sumGEZero.isUnsatisfiable()) {
                        if (Globals.DEBUG_FUHS && CondVarPolynomial.log.isLoggable(Level.FINEST)) {
                            CondVarPolynomial.log.finest(sumGEZero + " cannot hold: New condition " +
                                    vpc + " inconsistent with old condition " +
                                    cThis + " => omitting\n");
                        }
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * @param vpc - does this condition necessarily hold for this?
     * @return true if vpc is among the conditions for this (and thus always
     *  holds if this takes the value poly); false if we do not know
     */
    public boolean conditionsEntail(VarPolyConstraint vpc) {
        // maybe the local condition is vpc
        if (this.condition != null && this.condition.equals(vpc)) {
            return true;
        }

        // maybe an argument has vpc as condition
        for (CondVarPolynomial cond : this.argumentConditions) {
            boolean argCondHolds = cond.conditionsEntail(vpc);
            if (argCondHolds) {
                return true;
            }
        }

        // all right, we don't know whether vpc really must always
        // hold if all conditions of this hold at the same time
        return false;
    }

    public boolean hasConditions() {
        if (this.condition != null) {
            return true;
        }
        if (this.argumentConditions.size() > 0) {
            return true;
        }
        return false;
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append(this.condsToString());
        if (b.length() > 0) { // there are conditions to be considered
            b.append(" => ");
        }
        b.append(this.poly);
        return b.toString();
    }

    public String condsToString() {
        StringBuilder b = new StringBuilder();
        boolean first = true;
        for (CondVarPolynomial condVP : this.argumentConditions) {
            String condsString = condVP.condsToString();
            if (first) {
                first = false;
            }
            else {
                if (condsString.length() > 0) {
                    b.append(" and ");
                }
            }
            b.append(condsString);
        }
        if (this.condition != null) {
            if (b.length() > 0) {
                b.append(" and ");
            }
            b.append(this.condition);
        }
        return b.toString();
    }

    /*
    public Iterator<VarPolyConstraint> iterator() {
        // TODO Auto-generated method stub
        return null;
    }

    private class CondItr implements Iterator<VarPolyConstraint> {

        Iterator<CondVarPolynomial> conditionsIterator;
        boolean checkedLocalCond;

        private CondItr() {
            this.conditionsIterator = CondVarPolynomial.this.argumentConditions.listIterator();
            this.checkedLocalCond = false;
        }

        public boolean hasNext() {
            if (! this.checkedLocalCond) {
                if (CondVarPolynomial.this.condition != null) {
                    return true;
                }
                else {
            }
        }

        public VarPolyConstraint next() {
            // TODO Auto-generated method stub
            return null;
        }

        public void remove() {
            // TODO Auto-generated method stub

        }

    }
    */
}
