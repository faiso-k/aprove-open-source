package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * Transforms a formula so that there are only literals.
 *
 * @author dickmeis
 * @version $Id$
 */

public class ToLiteralsTransformerVisitor implements FineFormulaVisitor<Formula> {

    private ToLiteralsTransformerVisitor(){}

    public static Formula apply(Formula formula){
        ImplicationTransformerVisitor implicationTransformer = new ImplicationTransformerVisitor();

        Formula newFormula = formula.apply(implicationTransformer);

        ToLiteralsTransformerVisitor toLiteralsTransformerVisitor = new ToLiteralsTransformerVisitor();

        Formula result = newFormula.apply(toLiteralsTransformerVisitor);

        return result;
    }

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

    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {
        System.err.println("Transformation of implications has not been correct.");

        return null;
    }

    @Override
    public Formula caseImplication(Implication implFormula) {
        System.err.println("Transformation of implications has not been correct.");

        return null;
    }

    /**
     * -(-A) ~~> A
     *
     * -(A \/ B) ~~> -A /\ -B
     *
     * -(A /\ B) ~~> -A \/ -B
     *
     * -TRUE ~~> FALSE
     *
     * -FALSE ~~> TRUE
     */
    @Override
    public Formula caseNot(Not notFormula) {

        Formula phi = notFormula.getLeft();

        Formula result;

        if (phi instanceof Not) {
            Not phiNot = (Not) phi;

            Formula notLeft = phiNot.getLeft();
            result = notLeft.apply(this);
        }
        else if (phi instanceof And) {
            And phiAnd = (And) phi;

            Formula andLeft = phiAnd.getLeft();
            Formula andRight = phiAnd.getRight();

            Formula notAndLeft = Not.create(andLeft);
            Formula notAndRight = Not.create(andRight);

            Formula or = Or.create(notAndLeft, notAndRight);

            result = or.apply(this);
        }
        else if (phi instanceof Or) {
            Or phiOr = (Or) phi;

            Formula orLeft = phiOr.getLeft();
            Formula orRight = phiOr.getRight();

            Formula notOrLeft = Not.create(orLeft);
            Formula notOrRight = Not.create(orRight);

            Formula and = And.create(notOrLeft, notOrRight);

            result = and.apply(this);
        }
        else if(phi.equals(FormulaTruthValue.TRUE)){
            result = FormulaTruthValue.FALSE;
        }
        else if(phi.equals(FormulaTruthValue.FALSE)){
            result = FormulaTruthValue.TRUE;
        }
        else{
            result = notFormula;
        }

        return result;
    }

    @Override
    public Formula caseEquation(Equation phi) {
        return phi.deepcopy();
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        return truthvalFormula.deepcopy();
    }

}
