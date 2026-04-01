package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Adapted from FormulaEvaluationUnderHypothesisVisitor
 *
 * @author dickmeis
 * @version $Id$
 */
public class FormulaOutermostEvaluationUnderHypothesisVisitor implements
        FineFormulaVisitor<Formula> {

    protected Set<HypothesisPair> hypothesesSet;

    protected int negativeCounter;

    private boolean noVariableHeuristic;

    public static Formula apply(Program program, Formula input,
            Set<HypothesisPair> hypothesisSet) {
        return FormulaOutermostEvaluationUnderHypothesisVisitor.apply(program, input, hypothesisSet, false);
    }

    public static Formula apply(Program program, Formula input,
            Set<HypothesisPair> hypothesisSet, boolean noVariableHeuristic) {

        Iterator<HypothesisPair> iterator = hypothesisSet.iterator();
        while (iterator.hasNext()) {

            Pair<Formula, Set<VariableSymbol>> hypothesis = iterator.next();

            if (hypothesis.y.isEmpty() && hypothesis.x.isEquation()) {

                Equation equation = (Equation) hypothesis.x;
                Symbol leftSymbol = equation.getLeft().getSymbol();
                Symbol rightSymbol = equation.getRight().getSymbol();

                if (program.isPredefFunctionSymbol(leftSymbol)
                        && leftSymbol.getName().startsWith("equal")
                        && rightSymbol.getName().equals("true")) {

                    AlgebraTerm leftTerm = equation.getLeft().getArgument(0);
                    AlgebraTerm rightTerm = equation.getLeft().getArgument(1);

                    if (leftTerm.isVariable()) {
                        AlgebraSubstitution substitution = AlgebraSubstitution.create();
                        substitution.put((VariableSymbol) leftTerm.getSymbol(),
                                rightTerm);

                        input = input.apply(substitution);

                        iterator.remove();

                        continue;
                    }

                    if (rightTerm.isVariable()) {
                        AlgebraSubstitution substitution = AlgebraSubstitution.create();
                        substitution.put(
                                (VariableSymbol) rightTerm.getSymbol(),
                                leftTerm);

                        input = input.apply(substitution);

                        iterator.remove();

                        continue;
                    }

                }

                if (program.isPredefFunctionSymbol(rightSymbol)
                        && rightSymbol.getName().startsWith("equal")
                        && leftSymbol.getName().equals("true")) {

                    AlgebraTerm leftTerm = equation.getRight().getArgument(0);
                    AlgebraTerm rightTerm = equation.getRight().getArgument(1);

                    if (leftTerm.isVariable()) {
                        AlgebraSubstitution substitution = AlgebraSubstitution.create();
                        substitution.put((VariableSymbol) leftTerm.getSymbol(),
                                rightTerm);

                        input = input.apply(substitution);

                        hypothesisSet.remove(hypothesis);

                        continue;
                    }

                    if (rightTerm.isVariable()) {
                        AlgebraSubstitution substitution = AlgebraSubstitution.create();
                        substitution.put(
                                (VariableSymbol) rightTerm.getSymbol(),
                                leftTerm);

                        input = input.apply(substitution);

                        hypothesisSet.remove(hypothesis);

                        continue;
                    }

                }

            }

        }

        return input
                .apply(new FormulaOutermostEvaluationUnderHypothesisVisitor(
                        hypothesisSet, noVariableHeuristic));
    }

    private FormulaOutermostEvaluationUnderHypothesisVisitor(
            Set<HypothesisPair> hypothesisSet, boolean noVariableHeuristic) {

        // init object's variables
        this.hypothesesSet = hypothesisSet;

        this.negativeCounter = 0;

        this.noVariableHeuristic = noVariableHeuristic;
    }

    @Override
    public Formula caseAnd(And and) {

        for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(and);

            if ((substitution != null)
                    && hypothesis.y.containsAll(substitution.getDomain())) {
                this.hypothesesSet.remove(hypothesis);
                return FormulaTruthValue.TRUE;
            }
        }

        if (this.negativeCounter == 0) {
            for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if (hypothesis.x.isImplication()) {
                    Implication implication = (Implication) hypothesis.x;
                    AlgebraSubstitution substitution = implication.getRight().matches(
                            and);
                    if (substitution == null
                            || !hypothesis.y.containsAll(substitution
                                    .getDomain())) {
                        continue;
                    }
                    this.hypothesesSet.remove(hypothesis);
                    return implication.getLeft().apply(substitution);
                }
            }
        }

        Formula leftFormula = and.getLeft().apply(this);
        Formula rightFormula = and.getRight().apply(this);

        return And.create(leftFormula, rightFormula);
    }

    @Override
    public Formula caseEquation(Equation phi) {

        Equation equation = (Equation) phi.deepcopy();

        /**
         * Check if hypothesis are applicable
         */
        for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(equation);
            if ((substitution != null)
                    && hypothesis.y.containsAll(substitution.getDomain())) {
                this.hypothesesSet.remove(hypothesis);
                return FormulaTruthValue.TRUE;
            }

        }

        for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution;
            Symbol symbol;

            if (hypothesis.x.isEquation()) {

                Equation hypoEq = (Equation)hypothesis.x;

                symbol = ((Equation) hypothesis.x).getLeft().getSymbol();

                AlgebraTerm eqLeft = equation.getLeft();
                AlgebraTerm eqRight = equation.getRight();

                AlgebraTerm hypoLeft = hypoEq.getLeft();
                AlgebraTerm hypoRight = hypoEq.getRight();

                try {

                    if (! this.noVariableHeuristic ||
                            ! (hypoLeft instanceof AlgebraVariable) ||
                            ((hypoLeft instanceof AlgebraVariable) && (hypoRight instanceof AlgebraVariable))) {
                         // if doing noVariableHeuristic
                         // skip if only one side is a variable

                        for (Position position : eqLeft.getPositionsWithSymbol(symbol)) {

                            substitution = ((Equation) hypothesis.x)
                                    .getLeft()
                                    .matches(
                                            equation.getLeft().getSubterm(position));

                            if (!hypothesis.y.containsAll(substitution.getDomain())
                                    || equation.getLeft().isConstructorGroundTerm()
                                    || equation.getLeft().isConstant()) {
                                continue;
                            }

                            Equation newEquation = Equation
                                    .create(
                                            equation.getLeft().replaceAt(
                                                    ((Equation) hypothesis.x)
                                                            .getRight().apply(
                                                                    substitution),
                                                    position), equation.getRight());

                            this.hypothesesSet.remove(hypothesis);
                            return newEquation;

                        }
                    }

                }
                catch (UnificationException e) {
                }

                symbol = ((Equation) hypothesis.x).getRight().getSymbol();

                try {

                    if (! this.noVariableHeuristic ||
                            ! (hypoRight instanceof AlgebraVariable)) {
                        // if doing noVariableHeuristic
                        // skip if only one side is a variable
                        for (Position position : eqRight
                                .getPositionsWithSymbol(symbol)) {

                            substitution = ((Equation) hypothesis.x).getRight()
                                    .matches(
                                            equation.getRight()
                                                    .getSubterm(position));

                            if (!hypothesis.y.containsAll(substitution.getDomain())
                                    || equation.getRight()
                                            .isConstructorGroundTerm()
                                    || equation.getRight().isConstant()) {
                                continue;
                            }

                            Equation newEquation = Equation.create(equation
                                    .getLeft(), equation.getRight().replaceAt(
                                    ((Equation) hypothesis.x).getLeft().apply(
                                            substitution), position));

                            this.hypothesesSet.remove(hypothesis);
                            return newEquation;

                        }
                    }
                }
                catch (UnificationException e) {
                }

            }
        }

        if (this.negativeCounter == 0) {
            for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if (hypothesis.x.isImplication()) {
                    Implication implication = (Implication) hypothesis.x;
                    AlgebraSubstitution substitution = implication.getRight().matches(
                            equation);
                    if (substitution == null
                            || !hypothesis.y.containsAll(substitution
                                    .getDomain())) {
                        continue;
                    }
                    this.hypothesesSet.remove(hypothesis);
                    return implication.getLeft().apply(substitution);
                }
            }

        }

        return equation;
    }

    @Override
    public Formula caseEquivalence(Equivalence equivalence) {

        for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(equivalence);

            if ((substitution != null)
                    && (hypothesis.y.containsAll(substitution.getDomain()))) {
                ;
                this.hypothesesSet.remove(hypothesis);
                return FormulaTruthValue.TRUE;
            }

        }

        if (this.negativeCounter == 0) {
            for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if (hypothesis.x.isImplication()) {
                    Implication implication = (Implication) hypothesis.x;
                    AlgebraSubstitution substitution = implication.getRight().matches(
                            equivalence);
                    if (substitution == null
                            || !hypothesis.y.containsAll(substitution
                                    .getDomain())) {
                        continue;
                    }
                    this.hypothesesSet.remove(hypothesis);
                    return implication.getLeft().apply(substitution);
                }
            }

        }

        this.negativeCounter++;
        Formula leftFormula = equivalence.getLeft().apply(this);
        Formula rightFormula = equivalence.getRight().apply(this);
        this.negativeCounter--;

        return Equivalence.create(leftFormula, rightFormula);
    }

    @Override
    public Formula caseImplication(Implication implication) {

        for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(implication);

            if ((substitution != null)
                    && (hypothesis.y.containsAll(substitution.getDomain()))) {
                this.hypothesesSet.remove(hypothesis);
                return FormulaTruthValue.TRUE;
            }

        }

        if (this.negativeCounter == 0) {
            for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if (hypothesis.x.isImplication()) {
                    Implication impl = (Implication) hypothesis.x;
                    AlgebraSubstitution substitution = impl.getRight().matches(
                            implication);
                    if (substitution == null
                            || !hypothesis.y.containsAll(substitution
                                    .getDomain())) {
                        continue;
                    }
                    this.hypothesesSet.remove(hypothesis);
                    return impl.getLeft().apply(substitution);
                }
            }
        }

        this.negativeCounter++;
        Formula leftFormula = implication.getLeft().apply(this);
        this.negativeCounter--;

        Formula rightFormula = implication.getRight().apply(this);

        return Implication.create(leftFormula, rightFormula);

    }

    @Override
    public Formula caseNot(Not not) {

        for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(not);

            if ((substitution != null)
                    && (hypothesis.y.containsAll(substitution.getDomain()))) {
                ;
                this.hypothesesSet.remove(hypothesis);
                return FormulaTruthValue.TRUE;
            }

        }

        if (this.negativeCounter == 0) {
            for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if (hypothesis.x.isImplication()) {
                    Implication implication = (Implication) hypothesis.x;
                    AlgebraSubstitution substitution = implication.getRight().matches(
                            not);
                    if (substitution == null
                            || !hypothesis.y.containsAll(substitution
                                    .getDomain())) {
                        continue;
                    }
                    this.hypothesesSet.remove(hypothesis);
                    return implication.getLeft().apply(substitution);
                }
            }
        }

        this.negativeCounter++;
        Formula leftFormula = not.getLeft().apply(this);
        this.negativeCounter--;

        return Not.create(leftFormula);
    }

    @Override
    public Formula caseOr(Or or) {

        for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(or);

            if ((substitution != null)
                    && (hypothesis.y.containsAll(substitution.getDomain()))) {
                this.hypothesesSet.remove(hypothesis);
                return FormulaTruthValue.TRUE;
            }

        }

        if (this.negativeCounter == 0) {
            for (Pair<Formula, Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if (hypothesis.x.isImplication()) {
                    Implication implication = (Implication) hypothesis.x;
                    AlgebraSubstitution substitution = implication.getRight().matches(
                            or);
                    if (substitution == null
                            || !hypothesis.y.containsAll(substitution
                                    .getDomain())) {
                        continue;
                    }
                    this.hypothesesSet.remove(hypothesis);
                    return implication.getLeft().apply(substitution);
                }
            }
        }

        Formula leftFormula = or.getLeft().apply(this);
        Formula rightFormula = or.getRight().apply(this);

        return Or.create(leftFormula, rightFormula);
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthValue) {
        return truthValue.deepcopy();
    }
}
