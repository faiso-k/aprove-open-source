/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.Orders.Utility.GPOLO;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 * Apply to OPC and use toString() afterwards.
 * Use reset() before applying again.
 */
public class OPCExportVisitor<C extends GPolyCoeff> extends ConstraintVisitor.ConstraintVisitorSkeleton<C> {

    private final Stack<String> stack = new Stack<String>();
    private final Stack<String> tabs = new Stack<String>();

    private final FlatteningVisitor<C, GPolyVar> fvInner;
    private final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;

    private final Export_Util eu;

    public OPCExportVisitor(final FlatteningVisitor <C, GPolyVar> fvInner,
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter,
            Export_Util eu) {
        this.fvInner = fvInner;
        this.fvOuter = fvOuter;
        this.eu = eu;
        this.reset();
    }

    public void reset() {
        this.stack.clear();
        this.tabs.clear();
        this.tabs.push("");
    }

    /**
     * An atom is being visited.
     * @param param The constraint.
     */
    @Override
    public void fcaseAtom(final OPCAtom<C> param) {
        // System.err.println("Depth ATOM " + tabs.size() + " " + param);
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth ATOM 2 " + tabs.size() + " " + param);
    }


    /**
     * An existential quantifier constraint is being visited.
     * @param param The constraint.
     * @param newConstraint The (new?) subconstraint.
     * @return Some new constraint.
     */
    @Override
    public OrderPolyConstraint<C> caseQuantifierE(
            final OPCQuantifierE<C> param,
            final OrderPolyConstraint<C> newConstraint) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        this.stack.push(t + "E: " + param.getQuantifiedVariables() + this.eu.cond_linebreak() + this.stack.pop());
        // System.err.println(stack.lastElement());
        return new OPCQuantifierE<C>(newConstraint,
                param.getQuantifiedVariables());
    }
    /**
     * A universal quantifier constraint is being visited.
     * @param param The constraint.
     * @param newConstraint The (new?) subconstraint.
     * @return Some new constraint.
     */
    @Override
    public OrderPolyConstraint<C> caseQuantifierA(
            final OPCQuantifierA<C> param,
            final OrderPolyConstraint<C> newConstraint) {
        // System.err.println("CASE A");
        this.tabs.pop();
        String t = this.tabs.lastElement();
        this.stack.push(t + "A: " + param.getQuantifiedVariables() + this.eu.cond_linebreak() + this.stack.pop());
        // System.err.println(stack.lastElement());
        return new OPCQuantifierA<C>(newConstraint,
                param.getQuantifiedVariables());
    }

    /**
     * An and constraint is being visited.
     * @param param The constraint.
     * @param newOperands The set of (new?) subconstraints.
     * @return Some new constraint.
     */
    @Override
    public OrderPolyConstraint<C> caseAnd(
            final OPCAnd<C> param,
            final Set<OrderPolyConstraint<C>> newOperands) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        StringBuilder sb = new StringBuilder();
        sb.append(t);
        sb.append("AND: ");
        sb.append(this.eu.cond_linebreak());
        for (OrderPolyConstraint<C> operand : newOperands) {
            sb.append(this.stack.pop());
            sb.append(this.eu.cond_linebreak());
        }
        this.stack.push(sb.toString());
        // System.err.println("caseAnd: " + stack.lastElement());
        return param;
    }

    /**
     * An or constraint is being visited.
     * @param param The constraint.
     * @param newOperands The set of (new?) left subconstraints.
     * @return Some new constraint.
     */
    @Override
    public OrderPolyConstraint<C> caseOr(
            final OPCOr<C> param,
            final Set<OrderPolyConstraint<C>> newOperands) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        StringBuilder sb = new StringBuilder();
        sb.append(t);
        sb.append("OR: ");
        sb.append(this.eu.cond_linebreak());
        for (OrderPolyConstraint<C> operand : newOperands) {
            sb.append(this.stack.pop());
            sb.append(this.eu.cond_linebreak());
        }
        this.stack.push(sb.toString());
        // System.err.println(stack.lastElement());
        return param;
    }

    /**
     * An atom is being visited.
     * @param param The constraint.
     * @return Some new constraint.
     */
    @Override
    public OrderPolyConstraint<C> caseAtom(final OPCAtom<C> param) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        StringBuilder sb = new StringBuilder();
        sb.append(t);
        sb.append("ATOM: ");
        sb.append(param.getLeftPoly().exportFlatDeep(this.fvInner, this.fvOuter, this.eu));
        sb.append(" ");
        sb.append(param.getConstraintType().export(this.eu));
        sb.append(" ");
        if (param.getRightPoly() != null) {
            sb.append(param.getRightPoly().exportFlatDeep(this.fvInner, this.fvOuter, this.eu));
        } else {
            sb.append("0");
        }
        this.stack.push(sb.toString());
        // System.err.println(stack.lastElement());
        return param;
    }

    /**
     * A true node is being visited.
     * @param param The constraint.
     * @return param itself.
     */
    @Override
    public OrderPolyConstraint<C> caseTrue(final OPCTrue<C> param) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        StringBuilder sb = new StringBuilder();
        sb.append(t);
        sb.append(param);
        this.stack.push(sb.toString());
        // System.err.println(stack.lastElement());
        return param;
    }

    /**
     * A logical variable node is being visited.
     * @param param The constraint.
     * @return param itself.
     */
    @Override
    public OrderPolyConstraint<C> caseLogVar(final OPCLogVar<C> param) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        StringBuilder sb = new StringBuilder();
        sb.append(t);
        sb.append(param);
        this.stack.push(sb.toString());
        // System.err.println(stack.lastElement());
        return param;
    }

    /**
     * A false node is being visited.
     * @param param The constraint.
     * @return param itself.
     */
    @Override
    public OrderPolyConstraint<C> caseFalse(final OPCFalse<C> param) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        StringBuilder sb = new StringBuilder();
        sb.append(t);
        sb.append(param);
        this.stack.push(sb.toString());
        // System.err.println(stack.lastElement());
        return param;
    }

    @Override
    public OrderPolyConstraint<C> caseComment(OPCComment<C> param,
            String comment, OrderPolyConstraint<C> sub) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        StringBuilder sb = new StringBuilder();
        sb.append(t);
        sb.append("COMMENT: ");
        sb.append(param.getComment());
        sb.append(this.eu.cond_linebreak());
        sb.append(this.stack.pop());
        this.stack.push(sb.toString());
        return param;
    }

    /**
     * A not node is being visited.
     * @param param the constraint
     * @param newConstraint the new subconstraint.
     * @return param itself.
     */
    @Override
    public OrderPolyConstraint<C> caseNot(final OPCNot<C> param,
            final OrderPolyConstraint<C> newConstraint) {
        this.tabs.pop();
        String t = this.tabs.lastElement();
        StringBuilder sb = new StringBuilder();
        sb.append(t);
        sb.append("NOT: ");
        sb.append(this.eu.cond_linebreak());
        sb.append(this.stack.pop());
        this.stack.push(sb.toString());
        // System.err.println(stack.lastElement());
        return param;
    }

    /**
     * An existential quantifier constraint is being visited.
     * @param param The constraint.
     */
    @Override
    public void fcaseQuantifierE(final OPCQuantifierE<C> param) {
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth " + tabs.size() + " " + param);
    }

    /**
     * A universal quantifier constraint is being visited.
     * @param param The constraint.
     */
    @Override
    public void fcaseQuantifierA(final OPCQuantifierA<C> param) {
        // System.err.println("Depth A " + tabs.size() + " " + param);
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth A2 " + tabs.size() + " " + param);
    }

    /**
     * An and constraint is being visited.
     * @param param The constraint.
     */
    @Override
    public void fcaseAnd(final OPCAnd<C> param) {
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth " + tabs.size() + " " + param);
    }

    /**
     * An or constraint is being visited.
     * @param param The constraint.
     */
    @Override
    public void fcaseOr(final OPCOr<C> param) {
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth " + tabs.size() + " " + param);
    }

    /**
     * A true node is being visited.
     * @param param The constraint.
     */
    @Override
    public void fcaseTrue(final OPCTrue<C> param) {
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth " + tabs.size() + " " + param);
    }

    /**
     * A logical variable node is being visited.
     * @param param The constraint.
     */
    @Override
    public void fcaseLogVar(OPCLogVar<C> param) {
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth " + tabs.size() + " " + param);
    }

    /**
     * A false node is being visited.
     * @param param The constraint.
     */
    @Override
    public void fcaseFalse(final OPCFalse<C> param) {
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth " + tabs.size() + " " + param);
    }

    /**
     * A comment node is being visited.
     * @param param the constraint
     */
    @Override
    public void fcaseComment(final OPCComment<C> param) {
        this.tabs.push(this.tabs.lastElement() + "\t");
    }

    /**
     * A not node is being visited.
     * @param param the constraint
     */
    @Override
    public void fcaseNot(final OPCNot<C> param) {
        this.tabs.push(this.tabs.lastElement() + "\t");
        // System.err.println("Depth " + tabs.size() + " " + param);
    }

    @Override
    public String toString() {
        if (this.stack.size() > 0) {
            StringBuilder sb = new StringBuilder();
            for (String string : this.stack) {
                sb.append(string);
                sb.append(this.eu.cond_linebreak());
            }
            return sb.toString();
        } else {
            return "OPCExporter not yet applied";
        }
    }
}
