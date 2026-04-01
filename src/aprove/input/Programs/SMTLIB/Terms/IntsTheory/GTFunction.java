package aprove.input.Programs.SMTLIB.Terms.IntsTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class GTFunction extends DiophanticFunction implements Immutable {
    private static final VariadicFunctionSort GTType =
        VariadicFunctionSort.create(SortInt.SORTINT, SortInt.SORTINT, 2);

    public GTFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(GTFunction.GTType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        final List<SimplePolynomial> sps = new LinkedList<SimplePolynomial>();
        for (final SMTTermWrapper t : arguments) {
            sps.add(t.getSimplePolynomial());
        }

        return new DiophantineFormulaWrapper(this.realApply(sps,
            ConstraintType.GT), this.formulaFactory);
    }
}
