package aprove.verification.oldframework.Logic.Formulas ;


/** formula(s) connected with a junctor.
 * @author  Burak
 * @version $Id$
 */
import java.util.*;

import aprove.verification.oldframework.Exceptions.*;

public abstract class JunctorFormula extends Formula
{
    protected Formula left;
    protected Formula right;

    public JunctorFormula() {
    }

    final public Formula getLeft() {
        return this.left;
    }

    final public void setLeft(Formula left) {
        this.left = left;
    }

    public Formula getRight() {
        // this method is overriden in Not - there it returns "null"
        return this.right;
    }

    final public void setRight(Formula right) {
        this.right = right;
    }

    protected JunctorFormula(Formula leftFormula, Formula rightFormula) {
        this.left = leftFormula;
        this.right = rightFormula;
    }

    @Override
    public <T> T apply( CoarseFormulaVisitor<T> cfv ) {
    return cfv.caseJunctorFormula( this );
    }

    @Override
    public <T> T apply(CoarseFormulaVisitorException<T> cfve) throws InvalidPositionException {
        return cfve.caseJunctorFormula(this);
    }

    @Override
    public boolean isAtomic() {
        return false;
    }

    @Override
    public boolean isEquation() {
        return false;
    }

    @Override
    public List<Formula> getArguments() {

        Vector<Formula> returnValue = new Vector<Formula>();

        returnValue.add(this.getLeft());
        returnValue.add(this.getRight());

        return returnValue;
    }

}
