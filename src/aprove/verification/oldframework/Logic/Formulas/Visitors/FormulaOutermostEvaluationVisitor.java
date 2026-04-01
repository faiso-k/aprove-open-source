/*
 * Created on 08.07.2004
 *
 */
package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * @author dickmeis
 * @version $Id$
 */
public class FormulaOutermostEvaluationVisitor implements
        FineFormulaVisitor<Formula>, CoarseGrainedTermVisitor<AlgebraTerm> {

    protected Program program;

    public static Formula apply(Formula formula, Program program) {

        FormulaOutermostEvaluationVisitor formulaEvaluationVisitor = new FormulaOutermostEvaluationVisitor(
                program);

        Formula newFormula = formula;

        while (!(newFormula = formula.apply(formulaEvaluationVisitor))
                .equals(formula)) {
            formula = newFormula;
        }

        return newFormula;
    }

    /**
     *
     * @param program
     */
    protected FormulaOutermostEvaluationVisitor(Program program) {

        // init object's variables
        this.program = program;
    }

    /**
     * Evaluates a subformula of the form "leftFormula /\ rightFormula"
     */
    @Override
    public Formula caseAnd(And and) {

        Formula newPhi = and.getLeft().apply(this);
        Formula newPsi = and.getRight().apply(this);

        if (newPhi.equals(FormulaTruthValue.FALSE) || newPsi.equals(FormulaTruthValue.FALSE)) {
            return FormulaTruthValue.FALSE;
        }

        if (newPhi.equals(FormulaTruthValue.TRUE) && newPsi.equals(FormulaTruthValue.TRUE)) {
            return FormulaTruthValue.TRUE;
        }

        if (newPhi.equals(FormulaTruthValue.TRUE)) {
            return newPsi;
        }

        if (newPsi.equals(FormulaTruthValue.TRUE)) {
            return newPhi;
        }

        return And.create(newPhi, newPsi);

    }

    /**
     * Evaluates a subformula of the form "leftTerm = rightTerm"
     */
    @Override
    public Formula caseEquation(Equation phi) {

        AlgebraTerm newLeftTerm  = phi.getLeft().apply(this);

        AlgebraTerm newRightTerm = phi.getRight().apply(this);

        if (newLeftTerm.equals(newRightTerm)) {
            return FormulaTruthValue.TRUE;
        }

        Sort newLeftTermSort = newLeftTerm.getSort();
        DefFunctionSymbol equalSymbol = newLeftTermSort.getEqualOp();

        List<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
        arguments.add(newLeftTerm);
        arguments.add(newRightTerm);
        AlgebraFunctionApplication functionApplication = AlgebraFunctionApplication.create(
                equalSymbol, arguments);

        for (Rule rule : this.program.getRules(equalSymbol)) {

            try {
                AlgebraSubstitution substitution = rule.getLeft().matches(
                        functionApplication);
                AlgebraTerm newTerm = rule.getRight().apply(substitution);

                if (newTerm.getSymbol().getName().equals("true")) {
                    return FormulaTruthValue.TRUE;
                }

                if (newTerm.getSymbol().getName().equals("false")) {
                    return FormulaTruthValue.FALSE;
                }

                Formula newFormula = TermToFormulaVisitor.apply(newTerm,
                        this.program).apply(this);
                return newFormula;
            }
            catch (UnificationException e) {
            }
        }

        return Equation.create(newLeftTerm, newRightTerm);
    }

    /**
     * Evaluates a subformula of the form "leftFormula <-> rightFormula"
     */
    @Override
    public Formula caseEquivalence(Equivalence equivalence) {

        if (equivalence.getLeft().equals(equivalence.getRight())) {
            return FormulaTruthValue.TRUE;
        }

        Formula newLeftFormula = equivalence.getLeft().apply(this);
        Formula newRightFormula = equivalence.getRight().apply(this);

        if ((newLeftFormula.equals(FormulaTruthValue.FALSE) && newRightFormula.equals(FormulaTruthValue.FALSE))
                || (newLeftFormula.equals(FormulaTruthValue.TRUE) && newRightFormula.equals(FormulaTruthValue.TRUE))) {

            return FormulaTruthValue.TRUE;

        }

        if (newRightFormula.equals(FormulaTruthValue.TRUE)) {
            return newLeftFormula;
        }

        if (newLeftFormula.equals(FormulaTruthValue.TRUE)) {
            return newRightFormula;
        }

        if (newLeftFormula.equals(FormulaTruthValue.FALSE)) {
            return Not.create(newRightFormula);
        }

        if (newRightFormula.equals(FormulaTruthValue.FALSE)) {
            return Not.create(newLeftFormula);
        }

        return Equivalence.create(newLeftFormula, newRightFormula);

    }

    /**
     * Evaluates a subformula of the form "leftFormula -> rightFormula"
     */
    @Override
    public Formula caseImplication(Implication implication) {

        Formula newLeftFormula = implication.getLeft().apply(this);
        Formula newRightFormula = implication.getRight().apply(this);

        if (newLeftFormula.equals(newRightFormula)) {
            return FormulaTruthValue.TRUE;
        }
        else if (newLeftFormula.equals(FormulaTruthValue.TRUE)) {
            return newRightFormula;
        }
        else if (newLeftFormula.equals(FormulaTruthValue.FALSE)) {
            return FormulaTruthValue.TRUE;
        }
        else if (newRightFormula.equals(FormulaTruthValue.FALSE)) {
            return Not.create(newLeftFormula);
        }
        else if (newRightFormula.equals(FormulaTruthValue.TRUE)) {
            return FormulaTruthValue.TRUE;
        }
        else {
            return Implication.create(newLeftFormula, newRightFormula);
        }

    }

    /**
     * Evaluates a subformula of the form "~leftFormula"
     */
    @Override
    public Formula caseNot(Not notFormula) {

        Formula newFormula;

        newFormula = (Formula) notFormula.getLeft().apply(this);

        if (newFormula instanceof FormulaTruthValue) {
            if (newFormula.equals(FormulaTruthValue.TRUE)) {
                return FormulaTruthValue.FALSE;
            }
            else {
                return FormulaTruthValue.TRUE;
            }
        }

        return Not.create(newFormula);
    }

    /**
     * Evaluates a subformula of the form "leftFormula \/ rightFormula"
     */
    @Override
    public Formula caseOr(Or orFormula) {

        Formula newPhi;
        Formula newPsi;

        newPhi = (Formula) orFormula.getLeft().apply(this);
        newPsi = (Formula) orFormula.getRight().apply(this);

        if (newPhi.equals(FormulaTruthValue.TRUE) || newPsi.equals(FormulaTruthValue.TRUE)) {
            return FormulaTruthValue.TRUE;
        }

        if (newPhi.equals(FormulaTruthValue.FALSE)) {
            return newPsi;
        }

        if (newPsi.equals(FormulaTruthValue.FALSE)) {
            return newPhi;
        }

        return Or.create(newPhi, newPsi);

    }

    /**
     * Returns the given truth value
     */
    @Override
    public Formula caseTruthValue(FormulaTruthValue truthValue) {
        return truthValue;
    }

    /**
     * Evaluates a term f(t_1, ... , t_n) mit a defined function symbol f
     */
    @Override
    public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication fappl) {

        if (!fappl.isMetaFunctionApplication()) {

            SyntacticFunctionSymbol fsym = fappl.getFunctionSymbol();

            // go through all rules for this function symbol

            Set<Rule> rulesForSymbol = this.program.getAllRules(fsym);

            if (rulesForSymbol != null) {
                for (Rule rule : rulesForSymbol) {

                    /* try to match lhs of a rule with term */
                    try {
                        AlgebraSubstitution subs = rule.getLeft().matches(fappl);
                        for (Rule cond : rule.getConds()) {
                            AlgebraTerm left;
                            AlgebraTerm newLeft = cond.getLeft().apply(subs);
                            do{
                                left = newLeft;
                                newLeft = left.apply(this);
                            } while(!left.equals(newLeft));

                            AlgebraTerm right;
                            AlgebraTerm newRigth = cond.getRight();
                            do{
                                right = newRigth;
                                newRigth = right.apply(this);
                            } while(!right.equals(newRigth));

                            AlgebraSubstitution s2 = right.matches(left);
                            subs = subs.compose(s2);
                        }
                        AlgebraTerm newTerm = rule.getRight().apply(subs);

                        return newTerm;
                    }
                    catch (UnificationException e) {
                        // cannot be matched to this rule
                        // so try another rule
                    }
                }
            }

            int size = fappl.getArguments().size();

            List<AlgebraTerm> newArguments = new ArrayList<AlgebraTerm>(size);

            for (int i = 0; i < size; i++) {
                newArguments.add(fappl.getArgument(i).apply(this));
            }

            AlgebraTerm newTerm = AlgebraFunctionApplication.create(fsym, newArguments);

            return newTerm;
        }

        throw new RuntimeException("Should not be applied to annotated terms");

    }

    /**
     * Returns a copy of the variable
     */
    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        return v.shallowcopy();
    }
}