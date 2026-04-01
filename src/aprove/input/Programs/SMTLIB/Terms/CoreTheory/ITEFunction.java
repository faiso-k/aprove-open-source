package aprove.input.Programs.SMTLIB.Terms.CoreTheory;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import immutables.*;

public class ITEFunction extends AbstractFunctionWrapper implements Immutable {
    private static final FunctionSort ITEType =
        FunctionSort.create(SortBool.SORTBOOL, SortBool.SORTBOOL,
            NativeSort.NATIVESORT, NativeSort.NATIVESORT);

    public ITEFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(ITEFunction.ITEType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        final AbstractSort sort = arguments.get(1).getSort();
        SMTTermWrapper t;

        if (sort instanceof SortBool) {
            t =
                this.applySortBool(arguments.get(0), arguments.get(1),
                    arguments.get(2));
        } else if (sort instanceof SortInt) {
            t =
                this.applySortInt(arguments.get(0), arguments.get(1),
                    arguments.get(2));
        } else {
            throw new UnsupportedSortException("if-then-else");
        }

        return t;
    }

    private SMTTermWrapper applySortBool(final SMTTermWrapper c,
        final SMTTermWrapper a,
        final SMTTermWrapper b) throws RecognitionException {
        if (!(a.getSort() instanceof SortBool && b.getSort() instanceof SortBool)) {
            throw new ArgumentMismatchException();
        }

        final Formula<Diophantine> formula =
            this.formulaFactory.buildIte(c.getDiophantineFormula(),
                a.getDiophantineFormula(), b.getDiophantineFormula());

        return new DiophantineFormulaWrapper(formula, this.formulaFactory);
    }

    private SMTTermWrapper applySortInt(final SMTTermWrapper c,
        final SMTTermWrapper a,
        final SMTTermWrapper b) throws RecognitionException {
        if (!(a.getSort() instanceof SortInt && b.getSort() instanceof SortInt)) {
            throw new ArgumentMismatchException();
        }

        /* if-then-else for integer sorts:
         * d REL ite(c,a,b) <=>
         *     c <-> (e > 0) [where e is a fresh variable]
         * and e >= 0
         * and 1 >= e
         * adn d REL (e*a + (1-e)*b)
         */

        final String symbol =
            FreshNameGenerator.FRESHNAMEGENERATOR.getFreshITE();
        final SimplePolynomial e = SimplePolynomial.create(symbol);

        /* t1 := e >= 0, t2 := 1 >= e, t3 := e > 0 */
        final TheoryAtom<Diophantine> t1 =
            this.formulaFactory.buildTheoryAtom(Diophantine.create(e,
                SimplePolynomial.ZERO, ConstraintType.GE)), t2 =
            this.formulaFactory.buildTheoryAtom(Diophantine.create(
                SimplePolynomial.ONE, e, ConstraintType.GE)), t3 =
            this.formulaFactory.buildTheoryAtom(Diophantine.create(e,
                SimplePolynomial.ZERO, ConstraintType.GT));

        /* constraints := c <-> (e > 0) and e >= 0 and 1 >= e */
        Formula<Diophantine> constraints =
            this.formulaFactory.buildIff(c.getDiophantineFormula(), t3);
        constraints = this.formulaFactory.buildAnd(constraints, t1, t2);
        this.addConstraints(constraints);

        /* pol := e*a + (1-e)*b = e*(a-b) + b */
        final SimplePolynomial pol =
            e.times(a.getSimplePolynomial().minus(b.getSimplePolynomial())).plus(
                b.getSimplePolynomial());

        return new SimplePolynomialWrapper(pol, this.formulaFactory);
    }
}
