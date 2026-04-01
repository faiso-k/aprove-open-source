package aprove.input.Programs.SMTLIB.Terms.IntsTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class MinusFunction extends AbstractFunctionWrapper implements Immutable {
    private static final VariadicFunctionSort MinusType =
        VariadicFunctionSort.create(SortInt.SORTINT, SortInt.SORTINT, 1);

    public MinusFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(MinusFunction.MinusType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        SimplePolynomial p = null;
        if (arguments.size() == 1) {
            p = arguments.get(0).getSimplePolynomial().negate();
        } else {
            for (final SMTTermWrapper t : arguments) {
                if (p == null) {
                    p = t.getSimplePolynomial();
                } else {
                    p = p.minus(t.getSimplePolynomial());
                }
            }
        }

        return new SimplePolynomialWrapper(p, this.formulaFactory);
    }
}
