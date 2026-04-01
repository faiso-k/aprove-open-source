/*
 * Created on 17.09.2004
 */
package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author rabe
 */
public class FormulaEvaluationUnderHypothesisVisitor implements FineFormulaVisitor<Formula> {

    protected Set<HypothesisPair> hypothesesSet;
    protected Stack<Formula> stack;
    protected int negativeCounter;
    private boolean noVariableHeuristic;

    public static Formula apply(Program program, Formula input,
            Set<HypothesisPair> hypothesisSet) {
        return FormulaEvaluationUnderHypothesisVisitor.apply(program, input, hypothesisSet, false);
    }

    public static Formula apply(Program program, Formula input,
            Set<HypothesisPair> hypothesisSet, boolean noVariableHeuristic) {

        Iterator<HypothesisPair> iterator = hypothesisSet.iterator();
        while(iterator.hasNext()) {

            Pair<Formula,Set<VariableSymbol>> hypothesis = iterator.next();

            if(hypothesis.y.isEmpty() && hypothesis.x.isEquation()) {

                Equation equation  = (Equation)hypothesis.x;
                Symbol leftSymbol  = equation.getLeft().getSymbol();
                Symbol rightSymbol = equation.getRight().getSymbol();

                if(program.isPredefFunctionSymbol(leftSymbol) && leftSymbol.getName().startsWith("equal") &&
                   rightSymbol.getName().equals("true")) {

                    AlgebraTerm leftTerm  = equation.getLeft().getArgument(0);
                    AlgebraTerm rightTerm = equation.getLeft().getArgument(1);

                    if(leftTerm.isVariable()) {
                        AlgebraSubstitution substitution = AlgebraSubstitution.create();
                        substitution.put((VariableSymbol)leftTerm.getSymbol(), rightTerm);

                        input = input.apply(substitution);

                        iterator.remove();

                        continue;
                    }

                    if(rightTerm.isVariable()) {
                        AlgebraSubstitution substitution = AlgebraSubstitution.create();
                        substitution.put((VariableSymbol)rightTerm.getSymbol(), leftTerm);

                        input = input.apply(substitution);

                        iterator.remove();

                        continue;
                    }

                }

                if(program.isPredefFunctionSymbol(rightSymbol) && rightSymbol.getName().startsWith("equal") &&
                   leftSymbol.getName().equals("true")) {

                    AlgebraTerm leftTerm  = equation.getRight().getArgument(0);
                    AlgebraTerm rightTerm = equation.getRight().getArgument(1);

                    if(leftTerm.isVariable()) {
                        AlgebraSubstitution substitution = AlgebraSubstitution.create();
                        substitution.put((VariableSymbol)leftTerm.getSymbol(), rightTerm);

                        input = input.apply(substitution);

                        hypothesisSet.remove(hypothesis);

                        continue;
                    }

                    if(rightTerm.isVariable()) {
                        AlgebraSubstitution substitution = AlgebraSubstitution.create();
                        substitution.put((VariableSymbol)rightTerm.getSymbol(), leftTerm);

                        input = input.apply(substitution);

                        hypothesisSet.remove(hypothesis);

                        continue;
                    }

                }

            }

        }

        return input.apply(new FormulaEvaluationUnderHypothesisVisitor(hypothesisSet, noVariableHeuristic));
    }

    private FormulaEvaluationUnderHypothesisVisitor(Set<HypothesisPair> hypothesisSet, boolean noVariableHeuristic ) {

        // init object's variables
        this.hypothesesSet = hypothesisSet;
        this.stack = new Stack<Formula>();

        this.negativeCounter = 0;

        this.noVariableHeuristic = noVariableHeuristic;
    }

    @Override
    public Formula caseAnd(And and) {

        and.getLeft().apply(this);
        and.getRight().apply(this);

        Formula rightFormula = this.stack.pop();
        Formula leftFormula  = this.stack.pop();

        for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(and);

            if((substitution != null) && hypothesis.y.containsAll(substitution.getDomain())) {
                this.hypothesesSet.remove(hypothesis);
                this.stack.push(FormulaTruthValue.TRUE);
                return this.stack.peek();
            }


        }

         if(this.negativeCounter==0) {
             for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                 if(hypothesis.x.isImplication()) {
                     Implication implication = (Implication)hypothesis.x;
                     AlgebraSubstitution substitution = implication.getRight().matches(and);
                     if( substitution==null || !hypothesis.y.containsAll(substitution.getDomain())) {
                         continue;
                     }
                     this.stack.push(implication.getLeft().apply(substitution));
                     this.hypothesesSet.remove(hypothesis);
                     return this.stack.peek();
                 }
             }

         }

        this.stack.push(And.create(leftFormula,rightFormula));
        return this.stack.peek();
    }


    @Override
    public Formula caseEquation(Equation phi) {

        Equation equation = (Equation)phi.deepcopy();

        /**
         * Check if hypothesis are applicable
         */
         for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(equation);
            if((substitution != null) && hypothesis.y.containsAll(substitution.getDomain())) {
                   this.stack.push(FormulaTruthValue.TRUE);
                this.hypothesesSet.remove(hypothesis);
                return this.stack.peek();
            }

         }


        for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution     substitution;
            Symbol            symbol;

            if (hypothesis.x.isEquation()) {

                symbol = ((Equation)hypothesis.x).getLeft().getSymbol();

                Equation hypoEq = (Equation)hypothesis.x;

                AlgebraTerm hypoLeft = hypoEq.getLeft();
                AlgebraTerm hypoRight = hypoEq.getRight();

                try {

                    if (! this.noVariableHeuristic ||
                            ! (hypoLeft instanceof AlgebraVariable) ||
                            ((hypoLeft instanceof AlgebraVariable) && (hypoRight instanceof AlgebraVariable))) {
                        // if doing noVariableHeuristic
                        // skip if only one side is a variable

                        for(Position position : equation.getLeft().getPositionsWithSymbol(symbol)) {

                            substitution = ((Equation)hypothesis.x).getLeft().matches(
                                equation.getLeft().getSubterm(position));

                            if( !hypothesis.y.containsAll(substitution.getDomain()) || equation.getLeft().isConstructorGroundTerm() ||
                                equation.getLeft().isConstant()) {
                                continue;
                            }

                            this.stack.push(Equation.create(equation.getLeft().replaceAt(
                                ((Equation)hypothesis.x).getRight().apply(substitution),
                                position),equation.getRight()));

                            this.hypothesesSet.remove(hypothesis);
                            return this.stack.peek();

                        }
                    }

                }catch(UnificationException e){}

                symbol = ((Equation)hypothesis.x).getRight().getSymbol();

                try {

                    if (! this.noVariableHeuristic ||
                            ! (hypoRight instanceof AlgebraVariable)) {
                        // if doing noVariableHeuristic
                        // skip if only one side is a variable

                        for(Position position : equation.getRight().getPositionsWithSymbol( symbol)) {

                            substitution = ((Equation)hypothesis.x).getRight().matches(
                                equation.getRight().getSubterm(position));


                            if( !hypothesis.y.containsAll(substitution.getDomain()) || equation.getRight().isConstructorGroundTerm() ||
                                equation.getRight().isConstant()) {
                                continue;
                            }

                            this.stack.push(Equation.create(equation.getLeft(),equation.getRight().
                                replaceAt(((Equation)hypothesis.x).getLeft().apply(substitution), position)));

                            this.hypothesesSet.remove(hypothesis);
                            return this.stack.peek();

                        }

                    }
                } catch (UnificationException e) {}

            }
        }

        if(this.negativeCounter==0) {
            for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if(hypothesis.x.isImplication()) {
                    Implication implication = (Implication)hypothesis.x;
                    AlgebraSubstitution substitution = implication.getRight().matches(equation);
                    if(substitution == null || !hypothesis.y.containsAll(substitution.getDomain())) {
                        continue;
                    }
                    this.stack.push(implication.getLeft().apply(substitution));
                    this.hypothesesSet.remove(hypothesis);
                    return this.stack.peek();
                }
            }

        }

        this.stack.push(equation);
        return this.stack.peek();
    }

    @Override
    public Formula caseEquivalence(Equivalence equivalence) {

        this.negativeCounter++;
        equivalence.getLeft().apply(this);
        equivalence.getRight().apply(this);
        this.negativeCounter--;

        Formula rightFormula = (Formula) this.stack.pop();
        Formula leftFormula = (Formula) this.stack.pop();

        for (Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(equivalence);

            if( (substitution != null) && (hypothesis.y.containsAll(substitution.getDomain())) ) {;
                this.hypothesesSet.remove(hypothesis);
                this.stack.push(FormulaTruthValue.TRUE);
                return this.stack.peek();
            }

        }

         if(this.negativeCounter==0) {
                for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                    if(hypothesis.x.isImplication()) {
                        Implication implication = (Implication)hypothesis.x;
                        AlgebraSubstitution substitution = implication.getRight().matches(equivalence);
                        if(substitution==null || !hypothesis.y.containsAll(substitution.getDomain())) {
                            continue;
                        }
                        this.stack.push(implication.getLeft().apply(substitution));
                        this.hypothesesSet.remove(hypothesis);
                        return this.stack.peek();
                    }
                }

         }

        this.stack.push(Equivalence.create(leftFormula, rightFormula));
        return this.stack.peek();
    }

    @Override
    public Formula caseImplication(Implication implication) {

        this.negativeCounter++;
        implication.getLeft().apply(this);
        this.negativeCounter--;

        Formula r = implication.getRight();
        r.apply(this);

        Formula rightFormula = (Formula) this.stack.pop();
        Formula leftFormula = (Formula) this.stack.pop();

        for (Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(implication);

            if((substitution != null) && (hypothesis.y.containsAll(substitution.getDomain()))) {
                this.hypothesesSet.remove(hypothesis);
                this.stack.push(FormulaTruthValue.TRUE);
                return this.stack.peek();
            }

        }

        if(this.negativeCounter==0) {
            for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if(hypothesis.x.isImplication()) {
                    Implication impl = (Implication)hypothesis.x;
                    AlgebraSubstitution substitution = impl.getRight().matches(implication);
                    if(substitution==null || !hypothesis.y.containsAll(substitution.getDomain())) {
                       continue;
                    }
                    this.stack.push(impl.getLeft().apply(substitution));
                    this.hypothesesSet.remove(hypothesis);
                    return this.stack.peek();
                }
            }
        }

        this.stack.push(Implication.create(leftFormula, rightFormula));
        return this.stack.peek();

    }


    @Override
    public Formula caseNot(Not not) {

        this.negativeCounter++;
        not.getLeft().apply(this);
        this.negativeCounter--;

        Formula leftFormula = (Formula) this.stack.pop();

        for (Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution = hypothesis.x.matches(not);

            if((substitution != null) && (hypothesis.y.containsAll(substitution.getDomain()))) {;
                this.hypothesesSet.remove(hypothesis);
                this.stack.push(FormulaTruthValue.TRUE);
                return this.stack.peek();
            }

        }

        if(this.negativeCounter==0) {
               for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                   if(hypothesis.x.isImplication()) {
                       Implication implication = (Implication)hypothesis.x;
                    AlgebraSubstitution substitution = implication.getRight().matches(not);
                    if(substitution==null || !hypothesis.y.containsAll(substitution.getDomain())) {
                        continue;
                    }
                    this.stack.push(implication.getLeft().apply(substitution));
                    this.hypothesesSet.remove(hypothesis);
                    return this.stack.peek();
                   }
               }
        }

        this.stack.push(Not.create(leftFormula));
        return this.stack.peek();
    }

    @Override
    public Formula caseOr(Or or) {

        or.getLeft().apply(this);
        or.getRight().apply(this);

        Formula rightFormula = (Formula) this.stack.pop();
        Formula leftFormula = (Formula) this.stack.pop();

        for (Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {

            AlgebraSubstitution substitution=hypothesis.x.matches(or);

            if((substitution != null) && (hypothesis.y.containsAll(substitution.getDomain()))) {
                this.hypothesesSet.remove(hypothesis);
                this.stack.push(FormulaTruthValue.TRUE);
                return this.stack.peek();
            }

        }

        if(this.negativeCounter==0) {
            for(Pair<Formula,Set<VariableSymbol>> hypothesis : this.hypothesesSet) {
                if(hypothesis.x.isImplication()) {
                    Implication implication = (Implication)hypothesis.x;
                    AlgebraSubstitution substitution = implication.getRight().matches(or);
                    if(substitution==null || !hypothesis.y.containsAll(substitution.getDomain())) {
                        continue;
                    }
                    this.stack.push(implication.getLeft().apply(substitution));
                    this.hypothesesSet.remove(hypothesis);
                    return this.stack.peek();
                }
            }
        }

        this.stack.push( Or.create(leftFormula, rightFormula));
        return this.stack.peek();
    }

    @Override
    public Formula caseTruthValue(FormulaTruthValue truthValue) {
        this.stack.push(truthValue.deepcopy());
        return this.stack.peek();
    }
}
