package aprove.verification.oldframework.Logic.Formulas;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.LemmaDatabase.Index.*;

/**
 * TRUE or FALSE.
 * @author  Burak,(eugen)
 */

public class FormulaTruthValue extends Formula {
    public static final FormulaTruthValue TRUE = FormulaTruthValue.create(true);
    public static final FormulaTruthValue FALSE = FormulaTruthValue.create(false);

    protected boolean b;

    public FormulaTruthValue() {
    }

    //contructor
    protected FormulaTruthValue(final boolean b) {
        this.b = b;
    }

    public static FormulaTruthValue create(final boolean b) {
        return new FormulaTruthValue(b);
    }

    //Accessor methods
    /**
     *@return booleab value of this object
     */
    public boolean getValue() {
        return this.b;
    }

    /**
     *@param b is the new value of this object
     */
    public void setValue(final boolean b) {
        this.b = b;
    }

    //misc. methods
    @Override
    public <T> T apply(final FineFormulaVisitor<T> fv) {

        return fv.caseTruthValue(this);
    }

    @Override
    public <T> T apply(final FineFormulaVisitorException<T> fve) throws InvalidPositionException {
        return fve.caseTruthValue(this);
    }

    @Override
    public <T> T apply(final CoarseFormulaVisitor<T> cfv) {
        return cfv.caseTruthValue(this);
    }

    @Override
    public <T> T apply(final CoarseFormulaVisitorException<T> cfve) throws InvalidPositionException {
        return cfve.caseTruthValue(this);
    }

    @Override
    public Formula deepcopy() {
        return FormulaTruthValue.create(this.getValue());
    }

    @Override
    public Formula shallowcopy() {
        return this.deepcopy();
    }

    @Override
    public boolean equals(final Object object) {

        FormulaTruthValue truthValue;

        if (object instanceof FormulaTruthValue) {

            truthValue = (FormulaTruthValue) object;

            return (this.b == truthValue.b);

        } else {

            return false;

        }
    }

    @Override
    public boolean isAtomic() {
        return true;
    }

    @Override
    public boolean isEquation() {
        return false;
    }

    @Override
    public IndexSymbol getRootIndexSymbol() {
        return new IndexTruthValueSymbol(this.b);
    }

    @Override
    public List<Formula> getArguments() {
        return new Vector<Formula>();
    }

    @Override
    public boolean isImplication() {
        return false;
    }

    @Override
    public AlgebraSubstitution matchesWithIdentities(final Formula that, final AlgebraSubstitution subs) throws UnificationException {
        if (this.equals(that)) {
            return subs;
        } else {
            throw new MatchFailureException("match failure", null, null);
        }
    }

}
