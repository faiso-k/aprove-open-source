package aprove.input.Programs.SMTLIB.Terms.CoreTheory;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class FalseConstant extends SMTTermWrapper implements Immutable {

    public FalseConstant(final FormulaFactory<Diophantine> formulaFactory) {
        super(SortBool.SORTBOOL, formulaFactory);
    }

    @Override
    public Formula<Diophantine> getDiophantineFormula() {
        return (this.formulaFactory.buildConstant(false));
    }
}
