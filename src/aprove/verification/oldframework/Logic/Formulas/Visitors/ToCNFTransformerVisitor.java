package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * Transforms a formula into its CNF
 *
 * @author dickmeis
 * @version $Id$
 */

public class ToCNFTransformerVisitor implements FineFormulaVisitor<Formula> {

    private ToCNFTransformerVisitor(){
    }

    public static Formula apply(Formula formula){
        Formula newFormula = ToLiteralsTransformerVisitor.apply(formula);

        ToCNFTransformerVisitor toCNFTransformerVisitor = new ToCNFTransformerVisitor();

        Formula result = newFormula.apply(toCNFTransformerVisitor);
        Formula oldresult = newFormula;

        while(!result.equals(oldresult)){
            oldresult = result;
            result = result.apply(toCNFTransformerVisitor);
        }

        return result;
    }

    /**
     * A \/ (B /\ C)
     * ~~>
     * (A \/ B) /\ (A \/ C)
     */
    @Override
    public Formula caseOr(Or orFormula) {
        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();

        Formula result;

        if (right instanceof And) {
            And and = (And) right;

            Formula orLeft = and.getLeft();
            Formula orRight = and.getRight();

            Formula newOr1 = Or.create(left, orLeft);
            Formula newOr2 = Or.create(left, orRight);

            Formula newAnd = And.create(newOr1, newOr2);

            result = newAnd.apply(this);
        }
        else if (left instanceof And) {
            And and = (And) left;

            Formula orLeft = and.getLeft();
            Formula orRight = and.getRight();

            Formula newOr1 = Or.create(orLeft, right);
            Formula newOr2 = Or.create(orRight, right);

            Formula newAnd = And.create(newOr1, newOr2);

            result = newAnd.apply(this);
        }
        else{
            Formula newLeft = left.apply(this);
            Formula newRight= right.apply(this);

            result = And.create(newLeft, newRight);
        }

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
