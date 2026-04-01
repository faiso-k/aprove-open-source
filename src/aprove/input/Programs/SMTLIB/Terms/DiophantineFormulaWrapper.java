package aprove.input.Programs.SMTLIB.Terms;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Encapsulates a Formula<Diophantine>.
 */
public class DiophantineFormulaWrapper extends SMTTermWrapper {

    private final Formula<Diophantine> formula;

    public DiophantineFormulaWrapper(final Formula<Diophantine> formula,
            final FormulaFactory<Diophantine> formulaFactory) {
        super(SortBool.SORTBOOL, formulaFactory);
        this.formula = formula;
    }

    @Override
    public Formula<Diophantine> getDiophantineFormula() {
        return this.formula;
    }
}
