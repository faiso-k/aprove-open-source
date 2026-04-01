package aprove.verification.oldframework.Logic.Formulas ;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;


/** an equivalence "phi is equivalent to psi"
 * @author  Burak
 * @version $Id$
 */

public class Equivalence extends JunctorFormula
{
    public Equivalence() {
    }

    protected Equivalence( Formula leftFormula, Formula rightFormula ) {
        super(leftFormula, rightFormula);
    }

    public static Equivalence create( Formula leftFormula, Formula rightFormula ) {
    return new Equivalence(leftFormula, rightFormula);
    }

    @Override
    final public <T> T apply( FineFormulaVisitor<T> fv ) {
    return fv.caseEquivalence( this );
    }

    @Override
    final public <T> T apply( FineFormulaVisitorException<T> fve )
            throws InvalidPositionException {
        return fve.caseEquivalence( this );
    }

    @Override
    public Formula deepcopy(){
        return Equivalence.create( (Formula)this.left.deepcopy(), (Formula)this.right.deepcopy() );
    }

    @Override
    public Formula shallowcopy(){
        return Equivalence.create(this.left,this.right);
    }

    @Override
    public boolean equals(Object object) {

        boolean     returnValue;
        Equivalence equivalence;

        if( object instanceof Equivalence ) {

            equivalence = (Equivalence)object;

            returnValue = this.getLeft().equals(equivalence.getLeft());

            returnValue = returnValue && this.getRight().equals(equivalence.getRight());

            return returnValue;

        } else {

            return false;

        }

    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexEquivalenceSymbol();
    }

    @Override
    public boolean isImplication() {
        return false;
    }

    @Override
    public AlgebraSubstitution matchesWithIdentities(Formula that, AlgebraSubstitution subs) throws UnificationException {

        if(!(that instanceof Equivalence)) {
            throw new MatchFailureException("match failure",null,null);
        }

        try{
            AlgebraSubstitution substitution = this.left.matchesWithIdentities(((Equivalence)that).getLeft(), subs);
            return this.right.matchesWithIdentities(((Equivalence)that).getRight(),substitution) ;
        }catch(UnificationException e){
            AlgebraSubstitution substitution = this.left.matchesWithIdentities(((Equivalence)that).getRight(), subs);
            return this.right.matchesWithIdentities(((Equivalence)that).getLeft(),substitution) ;
        }
    }
}
