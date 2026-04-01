package aprove.verification.oldframework.Logic.Formulas ;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;


/** phi AND psi.
 * @author  Burak, Eugen
 * @version $Id$
 */

public class And extends JunctorFormula
{

    public And(){
    }

    protected And( Formula leftFormula, Formula rightFormula ) {
        super(leftFormula, rightFormula);
    }

    public static And create( Formula leftFormula, Formula rightFormula ) {
        return new And(leftFormula, rightFormula);
    }

    public static Formula create(List<? extends Formula> formulas) {
        if(formulas.size()==0) {
            return null;
        }else if(formulas.size()==1){
            return formulas.get(0).deepcopy();
        }else{
            And and = And.create(formulas.get(0).deepcopy(), formulas.get(1).deepcopy());
            for(int i=2; i < formulas.size(); i++) {
                and = And.create(and, formulas.get(i).deepcopy());
            }
            return and;
        }
    }

    public static Formula create(Collection<? extends Formula> formulas) {
        return And.create(new Vector<Formula>(formulas));
    }

    @Override
    final public <T> T apply( FineFormulaVisitor<T> fv ) {
        return fv.caseAnd( this );
    }

    @Override
    final public <T> T apply( FineFormulaVisitorException<T> fv )
            throws InvalidPositionException{
        return fv.caseAnd( this );
    }

    @Override
    public Formula deepcopy(){
        return And.create( this.left.deepcopy(), this.right.deepcopy() );
    }

    @Override
    public Formula shallowcopy(){
        return And.create(this.left,this.right );
    }

    @Override
    public boolean equals(Object object) {

        And     and;
        boolean returnValue;

        if( object instanceof And ) {

            and = (And)object;

            returnValue = this.getLeft().equals(and.getLeft());

            returnValue = returnValue && this.getRight().equals(and.getRight());

            return returnValue;

        } else {

            return false;

        }

    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexAndSymbol();
    }

    @Override
    public boolean isImplication() {
        return false;
    }

    @Override
    public AlgebraSubstitution matchesWithIdentities(Formula that, AlgebraSubstitution subs) throws UnificationException {

        if(!(that instanceof And)) {
            throw new MatchFailureException("match failure",null,null);
        }

        try {
            AlgebraSubstitution substitution = this.left.matchesWithIdentities(((And)that).getLeft(), subs);
            return this.right.matchesWithIdentities(((And)that).getRight(),substitution) ;
        }catch(UnificationException e) {
            AlgebraSubstitution substitution = this.left.matchesWithIdentities(((And)that).getRight(), subs);
            return this.right.matchesWithIdentities(((And)that).getLeft(),substitution) ;
        }
    }


}
