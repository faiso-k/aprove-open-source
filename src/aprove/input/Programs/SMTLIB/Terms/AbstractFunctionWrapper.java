package aprove.input.Programs.SMTLIB.Terms;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

/**
 * Encapsulates a function.
 */
public abstract class AbstractFunctionWrapper extends SMTTermWrapper implements
        Immutable {
    private final AbstractFunctionSort type;

    public AbstractFunctionWrapper(final AbstractFunctionSort sort,
            final FormulaFactory<Diophantine> formulaFactory) {
        super(sort, formulaFactory);
        this.type = sort;
    }

    /**
     * Applies the function to the arguments. Checks wether the arguments fit
     * and then calls realApply().
     * @return the result of the application
     */
    @Override
    public SMTTermWrapper apply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        if (!this.type.checkSort(arguments)) {
            throw new ArgumentMismatchException();
        }

        //this.resetConstraints();
        final SMTTermWrapper term = this.realApply(arguments);
        this.addConstraintsFromTerms(arguments);
        term.addConstraints(this.getConstraints());
        this.resetConstraints();

        return term;
    }

    public abstract SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException;
}
