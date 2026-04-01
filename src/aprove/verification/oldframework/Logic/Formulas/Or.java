package aprove.verification.oldframework.Logic.Formulas ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;


/** phi AND psi.
 * @author  Burak
 * @version $Id$
 */

public class Or extends JunctorFormula
{
    public Or() {
    }

    protected Or( Formula leftFormula, Formula rightFormula ) {
           super(leftFormula, rightFormula);
    }

    public static Or create( Formula leftFormula, Formula rightFormula ) {
    return new Or(leftFormula, rightFormula);
    }

    public static Formula create(List<Formula> formulas) {
        if(formulas.size()==0) {
            return null;
        }else if(formulas.size()==1){
            return formulas.get(0);
        }else{
            Or or = Or.create(formulas.get(0), formulas.get(1));
            for(int i=2; i < formulas.size(); i++) {
                or = Or.create(or, formulas.get(i).deepcopy());
            }
            return or;
        }
    }

    @Override
    final public <T> T apply( FineFormulaVisitor<T> fv ) {
        return fv.caseOr( this );
    }

    @Override
    final public <T> T apply( FineFormulaVisitorException<T> fve )
            throws InvalidPositionException {
        return fve.caseOr( this );
    }

    @Override
    public Formula deepcopy(){
        return Or.create( this.left.deepcopy(), this.right.deepcopy() );
    }

    @Override
    public Formula shallowcopy(){
        return Or.create(this.left,this.right);
    }

    @Override
    public boolean equals( Object object ) {

        Or or;
        boolean returnValue;

        if( object instanceof Or ) {

            or = (Or)object;

            returnValue = this.getLeft().equals(or.getLeft());

            returnValue = returnValue && this.getRight().equals(or.getRight());

            return returnValue;

        } else {

            return false;

        }

    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexOrSymbol();
    }

    @Override
    public boolean isImplication() {
        return false;
    }

    @Override
    public AlgebraSubstitution matchesWithIdentities(Formula that, AlgebraSubstitution subs) throws UnificationException {

        if(!(that instanceof Or)) {
            throw new MatchFailureException("match failure",null,null);
        }

        try {
            AlgebraSubstitution substitution = this.left.matchesWithIdentities(((Or)that).getLeft(), subs);
            return this.right.matchesWithIdentities(((Or)that).getRight(),substitution) ;
        } catch (UnificationException e) {
            AlgebraSubstitution substitution = this.left.matchesWithIdentities(((Or)that).getRight(), subs);
            return this.right.matchesWithIdentities(((Or)that).getLeft(),substitution) ;
        }
    }
}
