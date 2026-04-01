/**
 * @author CKuknat
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

/**
 * This abstract class provides the basic methods that can be used to travers
 * through the formula in a standard way.
 * @param <C> The coefficients used in the constraints' polynomials.
 * @author CKuknat
 */
public abstract class AbstractFormulaPolyExtractor<C extends GPolyCoeff>
    extends ConstraintVisitor.ConstraintVisitorSkeleton<C> {
    /**
     * Every new variable has a unique suffix defined by this number.
     */
    private int varCount;

    /**
     * A formula factory used to create the constraints.
     */
    private FormulaFactory<OPCAtom<MbyN>> formulaFactory = new FullSharingFlatteningFactory<OPCAtom<MbyN>>();

    /**
     * Collect all the constraints.
     */
    private Formula<OPCAtom<MbyN>> formula =
        this.formulaFactory.buildConstant(true);

    /**
     * Remember the quantifiers along the path to the atom.
     */
    private Stack<OPCQuantifier<C>> quantStack =
        new Stack<OPCQuantifier<C>>();

    /**
     * When negating a partial formula will be backed up here.
     */
    private Stack<Formula<OPCAtom<MbyN>>> backup = new Stack<Formula<OPCAtom<MbyN>>>();

    /**
     * @return a fresh variable.
     */
    protected GPolyVar newVar() {
        this.varCount++;
        String name = "x_" + this.varCount;
        return GAtomicVar.createVariable(name);
    }

    /**
     * An or node is visited, not supported.
     * @param or The or node.
     */
    @Override
    public void fcaseOr(final OPCOr<C> or) {
        if (Globals.useAssertions) {
            assert (false) : "Not supported.";
        }
    }

    /**
     * An existential quantifier is visited.
     * As only one existential quantifier is allowed and it must be at the root
     * of the formula, this will be checked.
     * @param quant The quantifier node.
     */
    @Override
    public void fcaseQuantifierE(final OPCQuantifierE<C> quant) {
        if (Globals.useAssertions) {
            assert (this.quantStack.empty())
            : "A existential quantifier may only appear at the formula's root!";
        }
        this.quantStack.push(quant);
    }

    /**
     * Remove the quantifier from the stack representing the path, as the
     * path starting with this quantifier is already handled now.
     * @param quant The quant node.
     * @param newConstraint the new and old sub constraint.
     * @return quant itself.
     */
    @Override
    public OPCQuantifierE<C> caseQuantifierE(
            final OPCQuantifierE<C> quant,
            final OrderPolyConstraint<C> newConstraint) {
        OPCQuantifier<C> pop = this.quantStack.pop();
        if (Globals.useAssertions) {
            assert (quant.equals(pop));
            assert (quant.getInnerConstraint().equals(newConstraint));
        }
        return quant;
    }

    /**
     * Start visiting the given constraint and clean up afterwards.
     * @param constraint The constraint that should be visited.
     * @return Some new constraint.
     */
    @Override
    public OrderPolyConstraint<C> applyToWithCleanup(final OrderPolyConstraint<C> constraint) {
        final OrderPolyConstraint<C> result = this.applyTo(constraint);
        this.formulaFactory = null;
        return result;
    }

    /**
     * A universal quantifier is visited. This visitor only allows these
     * quantifiers directly in front of a atom node.
     * @param quant The quantifier node.
     */
    @Override
    public void fcaseQuantifierA(final OPCQuantifierA<C> quant) {
        OrderPolyConstraint<C> inner = quant.getInnerConstraint();
        if (Globals.useAssertions) {
            assert (inner instanceof OPCAtom<?>)
            : "A universal quantifier may only be placed in front of an atom!";
            Set<GPolyVar> vars = new LinkedHashSet<GPolyVar>();
            for (OPCQuantifier<C> elem : this.quantStack) {
                vars.addAll(elem.getQuantifiedVariables());
            }
            assert (!vars.removeAll(quant.getQuantifiedVariables()))
            : "The quantified variables must be disjoint in every subformula";
        }
        this.quantStack.push(quant);
    }

    /**
     * Remove the quantifier from the stack representing the path, as the
     * path starting with this quantifier is already handled now.
     * @param quant The quant node.
     * @param newConstraint The new and old sub constraint.
     * @return quant itself.
     */
    @Override
    public OrderPolyConstraint<C> caseQuantifierA(
            final OPCQuantifierA<C> quant,
            final OrderPolyConstraint<C> newConstraint) {
        OPCQuantifier<C> pop = this.quantStack.pop();
        if (Globals.useAssertions) {
            assert (quant.getInnerConstraint().equals(newConstraint));
            assert (quant.equals(pop));
        }
        return quant;
    }

    /**
     * A not node is being visited.
     * @param not The not node.
     */
    @Override
    public void fcaseNot(final OPCNot<C> not) {
        if (Globals.useAssertions) {
            assert (not.getSub() instanceof OPCAnd<?> || not.getSub() instanceof OPCAtom<?>)
            : "NOT may only be used in front of AND or an Atom";
        }
        // the to-be-constructed formula for the nodes behind this and node
        // must be negated. To do that first backup the current formula,
        // collect the formula for the subnodes and negate that when
        // construction is finished. After that restore the old formula
        // from the backup. See caseAnd().
        this.backup.push(this.formula);
        this.formula = this.formulaFactory.buildConstant(true);
    }

    /**
     * Negate the result which is stored in this.formula. The original formula
     * is stored in this.backup.
     * @param not The not node.
     * @param newConstraint the new subconstraint.
     * @return not itself.
     */
    @Override
    public OrderPolyConstraint<C> caseNot(
            final OPCNot<C> not,
            final OrderPolyConstraint<C> newConstraint) {
        if (Globals.useAssertions) {
            assert (not.getSub().equals(newConstraint));
        }
        if (this.backup != null) {
            // negate the formula for this and node
            // (the previous formula is only stored in backup!).
            this.buildNot(this.formula);
            // re-apply the backup
            this.buildAnd(this.backup.pop(), this.formula);
        }
        return not;
    }

    /**
     * @return the collected constraints.
     */
    public Formula<OPCAtom<MbyN>> getFormula() {
        return this.formula;
    }

    /**
     * Negate the given formula and store the result in this.formula.
     * @param sub The formula to negate.
     */
    protected void buildNot(final Formula<OPCAtom<MbyN>> sub) {
        this.formula = this.formulaFactory.buildNot(sub);
    }

    /**
     * Build the conjunction of the formulae a and b, store the result in
     * this.formula.
     * @param a Subformula 1.
     * @param b Subformula 2.
     */
    protected void buildAnd(final Formula<OPCAtom<MbyN>> a,
            final Formula<OPCAtom<MbyN>> b) {
        this.formula = this.formulaFactory.buildAnd(a, b);
    }

    /**
     * @return the formula factory.
     */
    protected FormulaFactory<OPCAtom<MbyN>> getFormulaFactory() {
        return this.formulaFactory;
    }

    /**
     * @return the quantifier stack.
     */
    protected Stack<OPCQuantifier<C>> getQuantStack() {
        return this.quantStack;
    }
}
