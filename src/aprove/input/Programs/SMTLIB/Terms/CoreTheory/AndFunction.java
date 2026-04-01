package aprove.input.Programs.SMTLIB.Terms.CoreTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class AndFunction extends AbstractFunctionWrapper implements Immutable {
    private static final VariadicFunctionSort AndType =
        VariadicFunctionSort.create(SortBool.SORTBOOL, SortBool.SORTBOOL, 2);

    public AndFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(AndFunction.AndType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        final List<Formula<Diophantine>> fmlae =
            new LinkedList<Formula<Diophantine>>();
        for (final SMTTermWrapper t : arguments) {
            fmlae.add(t.getDiophantineFormula());
        }

        return new DiophantineFormulaWrapper(
            this.formulaFactory.buildAnd(fmlae), this.formulaFactory);
    }
}
