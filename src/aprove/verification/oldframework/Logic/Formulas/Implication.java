package aprove.verification.oldframework.Logic.Formulas ;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;


/** an implication "from phi follows psi"
 * Eugen: We assume that the meaning of this class shall be "phi -> psi"
 *        and not  "psi->phi"
 * @author  Burak
 * @version $Id$
 */

public class Implication extends JunctorFormula
{
    public Implication() {
    }

    protected Implication( Formula leftFormula, Formula rightFormula ) {
        super(leftFormula, rightFormula);
    }

    public static Implication create( Formula leftFormula, Formula rightFormula ) {
        return new Implication(leftFormula, rightFormula);
    }

    @Override
    final public <T>  T apply(FineFormulaVisitor<T> fv ) {
        return fv.caseImplication( this );
    }

    @Override
    final public <T>  T apply(FineFormulaVisitorException<T> fve )
            throws InvalidPositionException {
        return fve.caseImplication( this );
    }

    @Override
    public Formula deepcopy(){
        return Implication.create( (Formula)this.left.deepcopy(), (Formula)this.right.deepcopy() );
    }

    @Override
    public Formula shallowcopy(){
        return Implication.create(this.left,this.right);
    }

    @Override
    public boolean equals(Object object) {

        boolean     returnValue;
        Implication implication;

        if( object instanceof Implication ) {

            implication = (Implication)object;

            returnValue = this.getLeft().equals( implication.getLeft() );

            returnValue = returnValue && this.getRight().equals( implication.getRight() );

            return returnValue;

        } else {

            return false;

        }

    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexImplicationSymbol();
    }

    @Override
    public boolean isImplication() {
        return true;
    }

    @Override
    public AlgebraSubstitution matchesWithIdentities(Formula that, AlgebraSubstitution subs) throws UnificationException {

        if(!(that instanceof Implication)) {
            throw new MatchFailureException("match failure",null,null);
        }

        AlgebraSubstitution substitution = this.left.matchesWithIdentities(((Implication)that).getLeft(), subs);
        return this.right.matchesWithIdentities(((Implication)that).getRight(),substitution) ;
    }
}
