package aprove.verification.oldframework.Logic.Formulas.Visitors ;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/** to apply a substitution to a formula
 * Note: safe
 * @author Burak, eugen
 * @version $Id$
 */

public class SubstitutionVisitor implements FineFormulaVisitor<Formula> {
    protected AlgebraSubstitution sigma;

    @Override
    public Formula caseTruthValue( FormulaTruthValue tv ){
        return tv.deepcopy();
    }

    @Override
    public Formula caseEquation( Equation eq ){
    return Equation.create(
            eq.getLeft().deepcopy().apply(this.sigma),
            eq.getRight().deepcopy().apply(this.sigma));

      }

    /** the negated formula case
     */
    @Override
    public Formula caseNot( Not notFormula ) {
        return Not.create(notFormula.getLeft().apply(this));
    }

    /** the "phi and psi" case
     */
    @Override
    public Formula caseAnd( And andFormula ) {
        return And.create(
            andFormula.getLeft().apply(this),
            andFormula.getRight().apply(this) );
    }

    /** the "phi or psi" case
     */
      @Override
    public Formula caseOr( Or orFormula ) {
         return Or.create(
             orFormula.getLeft().apply(this),
             orFormula.getRight().apply(this));
    }

    /** the "from phi follows psi" case
     */
    @Override
    public Formula caseImplication( Implication implFormula ) {
        return Implication.create(
            implFormula.getLeft().apply(this),
            implFormula.getRight().apply(this));
    }

    /** the "phi is equiv. to psi" case
     */
    @Override
    public Formula caseEquivalence( Equivalence equivFormula ) {
        return Equivalence.create(
                equivFormula.getLeft().apply(this),
                equivFormula.getRight().apply(this));
    }

    protected SubstitutionVisitor( AlgebraSubstitution sigma ) {
        this.sigma = sigma;
    }

    /** returns a new formula which is equals sigma( phi )
     */
    public static Formula apply( AlgebraSubstitution sigma, Formula phi ) {
        SubstitutionVisitor sv = new SubstitutionVisitor( sigma );
        return (Formula) phi.apply( sv );

    }

}
