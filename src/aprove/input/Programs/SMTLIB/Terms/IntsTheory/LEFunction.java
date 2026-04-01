package aprove.input.Programs.SMTLIB.Terms.IntsTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class LEFunction extends DiophanticFunction implements Immutable {
    private static final VariadicFunctionSort LEType =
        VariadicFunctionSort.create(SortInt.SORTINT, SortInt.SORTINT, 2);

    public LEFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(LEFunction.LEType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        final List<SimplePolynomial> sps = new LinkedList<SimplePolynomial>();
        for (final SMTTermWrapper t : arguments) {
            sps.add(0, t.getSimplePolynomial());
        }

        return new DiophantineFormulaWrapper(this.realApply(sps,
            ConstraintType.GE), this.formulaFactory);
    }
}
