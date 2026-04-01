package aprove.verification.oldframework.Logic.Formulas ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;


/** negated formula.
 * @author  Burak
 * @version $Id$
 */

public class Not extends JunctorFormula
{
    public Not() {
    }

    @Override
    final public Formula getRight() {
        return null;
    }

    protected Not( Formula leftFormula ) {
        super( leftFormula, null );
    }

    public static Not create( Formula phi ) {
    return new Not(phi);
    }

    @Override
    final public <T> T apply( FineFormulaVisitor<T> fv ) {
        return fv.caseNot( this );
    }

    @Override
    final public <T> T apply( FineFormulaVisitorException<T> fve )
            throws InvalidPositionException {
        return fve.caseNot( this );
    }

    @Override
    public <T> T apply( CoarseFormulaVisitor<T> cfv ) {
        return cfv.caseJunctorFormula( this );
    }


    @Override
    public Formula deepcopy(){
        return Not.create( this.left.deepcopy() );
    }

    @Override
    public Formula shallowcopy(){
        return Not.create(this.left);
    }

    @Override
    public boolean equals(Object object) {

        Not not;

        if( object instanceof Not ) {

            not = (Not)object;

            return this.getLeft().equals( not.getLeft() );

        } else {

            return false;

        }
    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexNotSymbol();
    }

    @Override
    public List<Formula> getArguments() {
        List<Formula> returnValue = new Vector<Formula>();
        returnValue.add(this.getLeft());

        return returnValue;
    }

    @Override
    public boolean isImplication() {
        return false;
    }

    @Override
    public AlgebraSubstitution matchesWithIdentities(Formula that, AlgebraSubstitution subs) throws UnificationException {

        if(!(that instanceof Not)) {
            throw new MatchFailureException("match failure",null,null);
        }

        return this.left.matchesWithIdentities(((Not)that).getLeft(),subs) ;
    }
}

