package aprove.input.Programs.SMTLIB.Terms.CoreTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class NotFunction extends AbstractFunctionWrapper implements Immutable {
    private static final FunctionSort NotType =
        FunctionSort.create(SortBool.SORTBOOL, SortBool.SORTBOOL);

    public NotFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(NotFunction.NotType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        return new DiophantineFormulaWrapper(
            this.formulaFactory.buildNot(arguments.get(0).getDiophantineFormula()),
            this.formulaFactory);
    }
}
