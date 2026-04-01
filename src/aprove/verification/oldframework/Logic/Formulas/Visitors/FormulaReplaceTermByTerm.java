package aprove.verification.oldframework.Logic.Formulas.Visitors;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * Finds a term in a formula and replaces it with another term.
 * You have to take care yourself that the terms have the same sort.
 *
 * Actually this visitor goes down to each equation and calls on its
 * terms "replaceTermByTerm".
 *
 * @author dickmeis
 * @version $Id$
 */

public class FormulaReplaceTermByTerm implements FineFormulaVisitor<Formula> {

    private AlgebraTerm find;
    private AlgebraTerm replace;

    private FormulaReplaceTermByTerm (AlgebraTerm find, AlgebraTerm replace){
        this.find = find;
        this.replace = replace;
    }

    public static Formula apply(Formula formula, AlgebraTerm find, AlgebraTerm replace){
        FormulaReplaceTermByTerm frt = new FormulaReplaceTermByTerm(find, replace);
        Formula newFormula = formula.apply(frt);
        return newFormula;
    }

    /**
     * call replaceTermByTerm on the terms
     */
    @Override
    public Formula caseEquation(Equation eqFormula) {
        AlgebraTerm left = eqFormula.getLeft();
        AlgebraTerm right = eqFormula.getRight();

        AlgebraTerm newLeft = left.replaceTermByTerm(this.find, this.replace);
        AlgebraTerm newRight = right.replaceTermByTerm(this.find, this.replace);

        return Equation.create(newLeft, newRight);
    }

    /**
     * nothing to do
     */
    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {
        return truthvalFormula.deepcopy();
    }

    /**
     * just descend
     */
    @Override
    public Formula caseAnd(And andFormula) {
        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();

        Formula newLeft = left.apply(this);
        Formula newRight = right.apply(this);

        return And.create(newLeft, newRight);
    }

    /**
     * just descend
     */
    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {
        Formula left = equivFormula.getLeft();
        Formula right = equivFormula.getRight();

        Formula newLeft = left.apply(this);
        Formula newRight = right.apply(this);

        return Equivalence.create(newLeft, newRight);
    }

    /**
     * just descend
     */
    @Override
    public Formula caseImplication(Implication implFormula) {
        Formula left = implFormula.getLeft();
        Formula right = implFormula.getRight();

        Formula newLeft = left.apply(this);
        Formula newRight = right.apply(this);

        return Implication.create(newLeft, newRight);
    }

    /**
     * just descend
     */
    @Override
    public Formula caseNot(Not notFormula) {
        Formula left = notFormula.getLeft();

        Formula newLeft = left.apply(this);

        return Not.create(newLeft);
    }

    /**
     * just descend
     */
    @Override
    public Formula caseOr(Or orFormula) {
        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();

        Formula newLeft = left.apply(this);
        Formula newRight = right.apply(this);

        return Or.create(newLeft, newRight);
    }

}
