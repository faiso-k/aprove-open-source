package aprove.input.Programs.SMTLIB.Terms.IntsTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class GEFunction extends DiophanticFunction implements Immutable {
    private static final VariadicFunctionSort GEType =
        VariadicFunctionSort.create(SortInt.SORTINT, SortInt.SORTINT, 2);

    public GEFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(GEFunction.GEType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        final List<SimplePolynomial> sps = new LinkedList<SimplePolynomial>();
        for (final SMTTermWrapper t : arguments) {
            sps.add(t.getSimplePolynomial());
        }

        return new DiophantineFormulaWrapper(this.realApply(sps,
            ConstraintType.GE), this.formulaFactory);
    }
}
