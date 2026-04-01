package aprove.input.Programs.SMTLIB.Terms;

import java.util.*;

import org.antlr.runtime.*;

import aprove.*;
import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Encapsulates Formula<Diophantine> to represent Boolean constraints and
 * SimplePolynomial to represent Integers. Also there can be functions where
 * some arguments can be applied to.
 */
public abstract class SMTTermWrapper {
    private final AbstractSort sort;
    private Formula<Diophantine> constraints = null;
    protected final FormulaFactory<Diophantine> formulaFactory;

    public SMTTermWrapper(final AbstractSort sort,
            final FormulaFactory<Diophantine> formulaFactory) {
        if (Globals.useAssertions) {
            assert sort != null;
            assert formulaFactory != null;
        }
        this.sort = sort;
        this.formulaFactory = formulaFactory;
    }

    public AbstractSort getSort() {
        return this.sort;
    }

    public void resetConstraints() {
        this.constraints = null;
    }

    public void setConstraints(final Formula<Diophantine> constraints) {
        this.constraints = constraints;
    }

    public void addConstraints(final Formula<Diophantine> constraints) {
        if (this.constraints == null) {
            this.setConstraints(constraints);
        } else if (constraints != null) {
            this.setConstraints(this.formulaFactory.buildAnd(
                this.constraints, constraints));
        }
    }

    public void addConstraintsFromTerms(final List<SMTTermWrapper> terms) {
        for (final SMTTermWrapper term : terms) {
            this.addConstraints(term.getConstraints());
        }
    }

    public Formula<Diophantine> getConstraints() {
        return this.constraints;
    }

    /**
     * If this container wraps a SimplePolynomial return it, otherwise throw
     * exception.
     * @return the wrapped SimplePolynomial
     * @throws TermSortException
     */
    public SimplePolynomial getSimplePolynomial() throws RecognitionException {
        throw new TermSortException("SimplePolynomial");
    }

    /**
     * If this container wraps a Formula<Diophantine> return it, otherwise throw
     * exception.
     * @return the wrapped Formula<Diophantine>
     * @throws TermSortException
     */
    public Formula<Diophantine> getDiophantineFormula()
            throws RecognitionException {
        throw new TermSortException("Formula<Diophantine>");
    }

    /**
     * If this container wraps a function, this method applies the function to a
     * list of wrapped arguments. Otherwise throw exception.
     * @return the result of the application
     * @throws TermSortException
     */
    protected SMTTermWrapper apply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        throw new TermSortException("a function");
    }
}
