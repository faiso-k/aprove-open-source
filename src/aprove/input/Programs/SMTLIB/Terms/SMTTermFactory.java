package aprove.input.Programs.SMTLIB.Terms;

import java.math.*;
import java.util.*;

import org.antlr.runtime.*;

import aprove.*;
import aprove.input.Programs.SMTLIB.*;
import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.input.Programs.SMTLIB.Namespaces.*;
import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A Factory to create SMT-LIB terms. This Factory is not static because to
 * build terms one must have the namespace of declared and defined identifiers.
 */
public class SMTTermFactory {
    private final SMTBenchmark script;
    private final SMTNamespace namespace;
    private final FormulaFactory<Diophantine> formulaFactory;
    private Formula<Diophantine> constraints;

    public SMTTermFactory(final SMTBenchmark script) {
        if (Globals.useAssertions) {
            assert script != null;
            assert script.getNamespace() != null;
            assert script.getFormulaFactory() != null;
        }
        this.script = script;
        this.namespace = script.getNamespace();
        this.formulaFactory = script.getFormulaFactory();
    }

    /**
     * Copy constructor. Creates a new namespace with factory.namespace as its
     * parent.
     * @param factory The factory
     */
    public SMTTermFactory(final SMTTermFactory factory) {
        if (Globals.useAssertions) {
            assert factory != null;
        }
        this.namespace = new SMTNamespace(factory.namespace);
        this.script = factory.script;
        this.formulaFactory = factory.formulaFactory;
        this.constraints = factory.constraints;
    }


    /**
     * Puts a new identifier binding (definition) in the namespace.
     * @param identifier The identifier
     * @param term The binding
     * @throws RecognitionException
     */
    public void addBinding(final String identifier, final SMTTermWrapper term)
            throws RecognitionException {
        final String fresh =
            FreshNameGenerator.FRESHNAMEGENERATOR.getFreshLET();
        SMTTermWrapper var;

        Formula<Diophantine> constraint;

        if (SortBool.SORTBOOL.equalsWith(term.getSort())) {
            this.namespace.define(identifier, term);
            return;
        } else if (SortInt.SORTINT.equalsWith(term.getSort())) {
            var =
                new SimplePolynomialWrapper(SimplePolynomial.create(fresh),
                    this.formulaFactory);

            final Pair<SimplePolynomial, SimplePolynomial> p =
                var.getSimplePolynomial().minus(term.getSimplePolynomial()).toPositivePair();

            constraint =
                this.formulaFactory.buildTheoryAtom(Diophantine.create(p.x, p.y,
                    ConstraintType.EQ));
            if (term.getConstraints() != null) {
                constraint =
                    this.formulaFactory.buildAnd(term.getConstraints(), constraint);
                term.resetConstraints();
            }
        } else {
            throw new UnsupportedSortException("let var-binding");
        }

        if (this.constraints == null) {
            this.constraints = constraint;
        } else {
            this.constraints =
                this.formulaFactory.buildAnd(this.constraints, constraint);
        }

        this.script.addLetVariable(fresh);

        this.namespace.define(identifier, var);
    }

    public void putConstraintsIntoTerm(final SMTTermWrapper term) {
        term.addConstraints(this.constraints);
        this.constraints = null;
    }


    public SMTTermWrapper create(final BigInteger constant) {
        return new SimplePolynomialWrapper(SimplePolynomial.create(constant),
            this.formulaFactory);
    }

    public SMTTermWrapper create(final String identifier)
            throws RecognitionException {

        if (!this.namespace.isDeclared(identifier)) {
            throw new UndeclaredException(identifier);
        }

        SMTTermWrapper t;
        if (this.namespace.isDefined(identifier)) {
            t = this.namespace.getDefinition(identifier);
        } else {
            throw new UndefinedException(identifier);
        }
        return t;
    }

    public SMTTermWrapper create(final String identifier,
        final List<SMTTermWrapper> arguments) throws RecognitionException {
        if( !this.namespace.isDefined(identifier) ) {
            throw new UndefinedException(identifier);
        }

        final SMTTermWrapper t = this.namespace.getDefinition(identifier);
        return t.apply(arguments);
    }
}
