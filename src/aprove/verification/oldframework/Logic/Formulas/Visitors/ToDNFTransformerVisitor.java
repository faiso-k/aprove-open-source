package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * Transforms a formula into its DNF
 *
 * @author dickmeis
 * @version $Id$
 */

public class ToDNFTransformerVisitor implements FineFormulaVisitor<Formula> {

    private ToDNFTransformerVisitor(){
    }

    public static Formula apply(Formula formula){
        Formula newFormula = ToLiteralsTransformerVisitor.apply(formula);

        ToDNFTransformerVisitor toDNFTransformerVisitor = new ToDNFTransformerVisitor();

        Formula result = newFormula.apply(toDNFTransformerVisitor);
        Formula oldresult = newFormula;

        while(!result.equals(oldresult)){
            oldresult = result;
            result = result.apply(toDNFTransformerVisitor);
        }

        return result;
    }

    /**
     * A /\ (B \/ C)
     * ~~>
     * (A /\ B) \/ (A /\ C)
     */
    @Override
    public Formula caseAnd(And andFormula) {
        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();

        Formula result;

        if (right instanceof Or) {
            Or or = (Or) right;

            Formula orLeft = or.getLeft();
            Formula orRight = or.getRight();

            Formula newAnd1 = And.create(left, orLeft);
            Formula newAnd2 = And.create(left, orRight);

            Formula newOr = Or.create(newAnd1, newAnd2);

            result = newOr.apply(this);
        }
        else if (left instanceof Or) {
            Or or = (Or) left;

            Formula orLeft = or.getLeft();
            Formula orRight = or.getRight();

            Formula newAnd1 = And.create(orLeft, right);
            Formula newAnd2 = And.create(orRight, right);

            Formula newOr = Or.create(newAnd1, newAnd2);

            result = newOr.apply(this);
        }
        else{
            Formula newLeft = left.apply(this);
            Formula newRight= right.apply(this);

            result = And.create(newLeft, newRight);
        }

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
        System.err.println("Transformation to literals has not been correct.");

        return null;
    }

    @Override
    public Formula caseImplication(Implication implFormula) {
        System.err.println("Transformation to literals has not been not correct.");

        return null;
    }

    /**
     * Because we have transformed to literals before,
     * we can return this literal and
     * need not to descend to the equation / truth value .
     */
    @Override
    public Formula caseNot(Not notFormula) {
        return notFormula.deepcopy();
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
