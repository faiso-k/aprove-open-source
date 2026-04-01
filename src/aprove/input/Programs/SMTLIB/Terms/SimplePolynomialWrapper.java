package aprove.input.Programs.SMTLIB.Terms;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Encapsulates a SimplePolynomial.
 */
public class SimplePolynomialWrapper extends SMTTermWrapper {

    private final SimplePolynomial pol;

    public SimplePolynomialWrapper(final SimplePolynomial pol,
            final FormulaFactory<Diophantine> formulaFactory) {
        super(SortInt.SORTINT, formulaFactory);
        this.pol = pol;
    }

    @Override
    public SimplePolynomial getSimplePolynomial() {
        return this.pol;
    }

}
