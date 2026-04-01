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
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class EqualsFunction extends AbstractFunctionWrapper implements
        Immutable {
    private static final VariadicFunctionSort EqualsType =
        VariadicFunctionSort.create(SortBool.SORTBOOL, NativeSort.NATIVESORT, 2);

    public EqualsFunction(final FormulaFactory<Diophantine> formulaFactory) {
        super(EqualsFunction.EqualsType, formulaFactory);
    }

    @Override
    public SMTTermWrapper realApply(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        final AbstractSort sort = arguments.get(0).getSort();

        SMTTermWrapper t;

        if (sort instanceof SortBool) {
            t = this.applySortBool(arguments);
        } else if (sort instanceof SortInt) {
            t = this.applySortInt(arguments);
        } else {
            throw new UnsupportedSortException("equals");
        }

        return t;
    }

    private SMTTermWrapper applySortBool(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        Formula<Diophantine> formula = null;

        for (final SMTTermWrapper t : arguments) {
            if (!(t.getSort() instanceof SortBool)) {
                throw new ArgumentMismatchException();
            }

            final Formula<Diophantine> f = t.getDiophantineFormula();
            if (formula == null) {
                formula = f;
            } else {
                formula = this.formulaFactory.buildIff(formula, f);
            }
        }

        return new DiophantineFormulaWrapper(formula, this.formulaFactory);
    }

    private SMTTermWrapper applySortInt(final List<SMTTermWrapper> arguments)
            throws RecognitionException {
        for (final SMTTermWrapper t : arguments) {
            if (!(t.getSort() instanceof SortInt)) {
                throw new ArgumentMismatchException();
            }
        }

        Formula<Diophantine> formula = null;

        final Iterator<SMTTermWrapper> I = arguments.iterator();
        SimplePolynomial p1 = I.next().getSimplePolynomial(), p2 = null;
        while (I.hasNext()) {
            p2 = I.next().getSimplePolynomial();

            final Pair<SimplePolynomial, SimplePolynomial> p =
                p1.minus(p2).toPositivePair();

            final TheoryAtom<Diophantine> t =
                this.formulaFactory.buildTheoryAtom(Diophantine.create(p.x,
                    p.y,
                    ConstraintType.EQ));
            if (formula == null) {
                formula = t;
            } else {
                formula = this.formulaFactory.buildAnd(formula, t);
            }

            p1 = p2;
        }

        return new DiophantineFormulaWrapper(formula, this.formulaFactory);
    }
}
