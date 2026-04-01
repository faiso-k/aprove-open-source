package aprove.input.Programs.SMTLIB.Terms.CoreTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class ImpliesFunction extends AbstractFunctionWrapper implements
        Immutable {
    private static final VariadicFunctionSort ImpliesType =
        VariadicFunctionSort.create(SortBool.SORTBOOL, SortBool.SORTBOOL, 2);

    public ImpliesFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(ImpliesFunction.ImpliesType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        final ListIterator<SMTTermWrapper> I =
            arguments.listIterator(arguments.size());
        Formula<Diophantine> formula = null;

        while (I.hasPrevious()) {
            final Formula<Diophantine> f = I.previous().getDiophantineFormula();
            if (formula == null) {
                formula = f;
            } else {
                formula = this.formulaFactory.buildImplication(f, formula);
            }
        }

        return new DiophantineFormulaWrapper(formula, this.formulaFactory);
    }
}
