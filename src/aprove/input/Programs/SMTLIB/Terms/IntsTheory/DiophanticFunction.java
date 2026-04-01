package aprove.input.Programs.SMTLIB.Terms.IntsTheory;

import java.util.*;

import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public abstract class DiophanticFunction extends AbstractFunctionWrapper
        implements
        Immutable {

    protected DiophanticFunction(final AbstractFunctionSort sort,
            final FormulaFactory<Diophantine> formulaFactory) {
        super(sort, formulaFactory);
    }

    protected Formula<Diophantine> realApply(final List<SimplePolynomial> sps,
        final ConstraintType ct) {
        Formula<Diophantine> formula = null;

        final Iterator<SimplePolynomial> I = sps.iterator();
        SimplePolynomial p1 = I.next(), p2 = null;
        while (I.hasNext()) {
            p2 = I.next();

            final Pair<SimplePolynomial, SimplePolynomial> p =
                p1.minus(p2).toPositivePair();

            final TheoryAtom<Diophantine> t =
                this.formulaFactory.buildTheoryAtom(Diophantine.create(p.x,
                    p.y, ct));
            if (formula == null) {
                formula = t;
            } else {
                formula = this.formulaFactory.buildAnd(formula, t);
            }

            p1 = p2;
        }

        return formula;
    }

}
