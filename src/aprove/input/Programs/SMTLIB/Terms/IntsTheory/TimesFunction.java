package aprove.input.Programs.SMTLIB.Terms.IntsTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class TimesFunction extends AbstractFunctionWrapper implements Immutable {
    private static final VariadicFunctionSort TimesType =
        VariadicFunctionSort.create(SortInt.SORTINT, SortInt.SORTINT, 2);

    public TimesFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(TimesFunction.TimesType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        SimplePolynomial p = null;
        for (final SMTTermWrapper t : arguments) {
            if (p == null) {
                p = t.getSimplePolynomial();
            } else {
                p = p.times(t.getSimplePolynomial());
            }
        }

        return new SimplePolynomialWrapper(p, this.formulaFactory);
    }
}
