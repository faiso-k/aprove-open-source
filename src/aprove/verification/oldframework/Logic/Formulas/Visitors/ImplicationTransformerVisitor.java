package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * Transfomrs a formula so that there are no implications
 *
 * @author dickmeis
 * @version $Id$
 */


class ImplicationTransformerVisitor implements FineFormulaVisitor<Formula> {

    @Override
    public Formula caseAnd(And andFormula) {
        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();

        Formula newLeft = left.apply(this);
        Formula newRight= right.apply(this);

        Formula result = And.create(newLeft, newRight);

        return result;
    }

    @Override
    public Formula caseOr(Or orFormula) {
        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();

        Formula newLeft = left.apply(this);
        Formula newRight= right.apply(this);

        Formula result = Or.create(newLeft, newRight);

        return result;
    }

    /**
     * A <-> B
     * ~~>
     * (A -> B) /\ (B -> A)
     */
    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {
        Formula left = equivFormula.getLeft();
        Formula right = equivFormula.getRight();

        Formula impl1 = Implication.create(left, right);
        Formula impl2 = Implication.create(right, left);

        Formula and = And.create(impl1, impl2);

        Formula result = and.apply(this);

        return result;
    }

    /**
     * A -> B
     * ~~>
     * -A \/ B
     */
    @Override
    public Formula caseImplication(Implication implFormula) {
        Formula left = implFormula.getLeft();
        Formula right = implFormula.getRight();

        Formula newLeft = Not.create(left);

        Formula or = Or.create(newLeft, right);

        Formula result = or.apply(this);

        return result;
    }

    @Override
    public Formula caseNot(Not notFormula) {
        Formula left = notFormula.getLeft();

        Formula newLeft = left.apply(this);

        Formula result = Not.create(newLeft);

        return result;
    }

    @Override
    public Formula caseEquation(Equation phi) {
        return phi;
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        return truthvalFormula;
    }

}
