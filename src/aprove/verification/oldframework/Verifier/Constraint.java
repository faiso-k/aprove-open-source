package aprove.verification.oldframework.Verifier;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** A pair of terms representing a constraint.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class Constraint extends AbstractConstraint implements PairOfTerms, java.io.Serializable {

    /** only for serialize
     */
    public Constraint() {
    }

    /** Class constructor specifying all attributes.
     *  For internal use only.
     */

    protected Constraint(AlgebraTerm left, AlgebraTerm right, int type) {
        super(left, right, type);
    }

    /** Public constructor specifying two terms.
     * @param left Left term of this pair.
     * @param right Right term of this pair.
     * @param type Type indicator.
     * @return New Constraint with the given attributes.
     * @see AlgebraTerm
     */
    public static Constraint create(AlgebraTerm left, AlgebraTerm right, int type) {
        return new Constraint(left, right, type);
    }

    /** Public constructor specifying a rule.
     * @param rule Rule to get terms from.
     * @param type Type indicator.
     * @return New Constraint with the given attributes.
     * @see Rule
     */
    public static Constraint create(Rule rule, int type) {
        return new Constraint(rule.getLeft(), rule.getRight(), type);
    }

    /** Public constructor specifying an equation.
     * @param eqn Equation to get terms from.
     * @param type Type indicator.
     * @return New Constraint with the given attributes.
     * @see Rule
     */
    public static Constraint create(TRSEquation eqn, int type) {
        return new Constraint(eqn.getOneSide(), eqn.getOtherSide(), type);
    }

    @Override
    public AlgebraTerm getLeft() {
        return (AlgebraTerm)this.left;
    }

    @Override
    public AlgebraTerm getRight() {
        return (AlgebraTerm)this.right;
    }

    @Override
    public boolean equals(Object o) {
        Constraint c = (Constraint)o;
        return this.left.equals(c.left) && this.right.equals(c.right) && (this.type == c.type);
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    public Set<SyntacticFunctionSymbol> getFunctionSymbols() {
        Set<SyntacticFunctionSymbol> funcs = this.getLeft().getFunctionSymbols();
        funcs.addAll(this.getRight().getFunctionSymbols());
        return funcs;
    }


    public boolean checkVars() {
        AlgebraTerm left = (AlgebraTerm)this.left;
        AlgebraTerm right = (AlgebraTerm)this.right;
        return left.getVars().containsAll(right.getVars());
    }

}
