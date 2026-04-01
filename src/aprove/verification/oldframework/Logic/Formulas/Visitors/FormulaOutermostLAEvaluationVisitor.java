/*
 * Created on 08.07.2004
 *
 */
package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProcedures.*;

/**
 * @author dickmeis
 */
public class FormulaOutermostLAEvaluationVisitor implements FineFormulaVisitor<Formula>, CoarseGrainedTermVisitor<AlgebraTerm> {

    private final Program program;

    private final LAProgramProperties laProgram;

    private final Stack<Position> positionStack;

    private final Formula formula;

    public static Formula apply(Formula formula, final Program program) {

        final FormulaOutermostLAEvaluationVisitor formulaOutermostLAEvaluationVisitor =
            new FormulaOutermostLAEvaluationVisitor(formula, program);

        Formula newFormula = formula;

        while (!(newFormula = formula.apply(formulaOutermostLAEvaluationVisitor)).equals(formula)) {
            formula = newFormula;
        }

        return newFormula;
    }

    /**
     * @param program
     */
    protected FormulaOutermostLAEvaluationVisitor(final Formula formula, final Program program) {

        // init object's variables
        this.program = program;
        this.laProgram = program.laProgramProperties;

        this.positionStack = new Stack<Position>();
        this.positionStack.push(Position.create());

        this.formula = formula;
    }

    /**
     * Evaluates a subformula of the form "leftFormula /\ rightFormula"
     */
    @Override
    public Formula caseAnd(final And and) {

        final Formula left = and.getLeft();
        final Formula right = and.getRight();

        final Position pos = this.positionStack.peek();

        final Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        final Formula newPhi = left.apply(this);

        final Position rPos = Position.create(pos);
        rPos.add(1);
        this.positionStack.push(rPos);

        final Formula newPsi = right.apply(this);

        this.positionStack.pop();

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
    public Formula caseEquation(final Equation phi) {

        final AlgebraTerm left = phi.getLeft();
        final AlgebraTerm right = phi.getRight();

        final Position pos = this.positionStack.peek();

        final Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        final AlgebraTerm newLeftTerm = left.apply(this);

        final Position rPos = Position.create(pos);
        rPos.add(1);
        this.positionStack.push(rPos);

        final AlgebraTerm newRightTerm = right.apply(this);

        this.positionStack.pop();

        if (newLeftTerm.equals(newRightTerm)) {
            return FormulaTruthValue.TRUE;
        }

        final List<AlgebraTerm> terms = new ArrayList<AlgebraTerm>(2);
        terms.add(newLeftTerm);
        terms.add(newRightTerm);

        if (this.laProgram != null && newLeftTerm.getSort().equals(this.laProgram.sortNat)) {
            final Set<AlgebraVariable> usedVariables = newLeftTerm.getVars();
            usedVariables.addAll(newRightTerm.getVars());
            final Pair<List<AlgebraTerm>, Map<AlgebraTerm, AlgebraVariable>> p =
                FunctionAbstractionVisitor.apply(terms, usedVariables, this.program);
            final List<AlgebraTerm> abstractTerms = p.x;

            final AlgebraTerm abstractLeft = abstractTerms.get(0);
            final AlgebraTerm abstractRight = abstractTerms.get(1);

            final LinearConstraint constraint =
                LinearConstraint.createEquation(abstractLeft, abstractRight, this.laProgram);
            if (constraint.getConstant().equals(Rational.zero) && constraint.getCoefficients().isEmpty()) {
                return FormulaTruthValue.TRUE;
            }
        }

        //        if(IsLATermVisitor.apply(newLeftTerm, laProgram) &&
        //                IsLATermVisitor.apply(newRightTerm, laProgram)){
        //            LinearConstraint constraint =
        //                LinearConstraint.createEquation(newLeftTerm, newRightTerm, laProgram);
        //            if(constraint.getConstant().equals(Rational.zero)
        //                    && constraint.getCoefficients().isEmpty()){
        //                return TruthValue.TRUE;
        //            }
        //        }

        final Sort newLeftTermSort = newLeftTerm.getSort();
        final DefFunctionSymbol equalSymbol = newLeftTermSort.getEqualOp();

        final List<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
        arguments.add(newLeftTerm);
        arguments.add(newRightTerm);
        final AlgebraFunctionApplication functionApplication = AlgebraFunctionApplication.create(equalSymbol, arguments);

        for (final Rule rule : this.program.getRules(equalSymbol)) {

            try {
                final AlgebraSubstitution substitution = rule.getLeft().matches(functionApplication);
                final AlgebraTerm newTerm = rule.getRight().apply(substitution);

                if (newTerm.getSymbol().getName().equals("true")) {
                    return FormulaTruthValue.TRUE;
                }

                if (newTerm.getSymbol().getName().equals("false")) {
                    return FormulaTruthValue.FALSE;
                }

                final Formula newFormula = TermToFormulaVisitor.apply(newTerm, this.program).apply(this);
                return newFormula;
            } catch (final UnificationException e) {
            }
        }

        return Equation.create(newLeftTerm, newRightTerm);

    }

    /**
     * Evaluates a subformula of the form "leftFormula <-> rightFormula"
     */
    @Override
    public Formula caseEquivalence(final Equivalence equivalence) {

        if (equivalence.getLeft().equals(equivalence.getRight())) {
            return FormulaTruthValue.TRUE;
        }

        final Formula left = equivalence.getLeft();
        final Formula right = equivalence.getRight();

        final Position pos = this.positionStack.peek();

        final Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        final Formula newLeftFormula = left.apply(this);

        final Position rPos = Position.create(pos);
        rPos.add(1);
        this.positionStack.push(rPos);

        final Formula newRightFormula = right.apply(this);

        this.positionStack.pop();

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
    public Formula caseImplication(final Implication implication) {

        final Formula left = implication.getLeft();
        final Formula right = implication.getRight();

        final Position pos = this.positionStack.peek();

        final Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        final Formula newLeftFormula = left.apply(this);

        final Position rPos = Position.create(pos);
        rPos.add(1);
        this.positionStack.push(rPos);

        final Formula newRightFormula = right.apply(this);

        this.positionStack.pop();

        if (newLeftFormula.equals(newRightFormula)) {
            return FormulaTruthValue.TRUE;
        } else if (newLeftFormula.equals(FormulaTruthValue.TRUE)) {
            return newRightFormula;
        } else if (newLeftFormula.equals(FormulaTruthValue.FALSE)) {
            return FormulaTruthValue.TRUE;
        } else if (newRightFormula.equals(FormulaTruthValue.FALSE)) {
            return Not.create(newLeftFormula);
        } else if (newRightFormula.equals(FormulaTruthValue.TRUE)) {
            return FormulaTruthValue.TRUE;
        } else {
            return Implication.create(newLeftFormula, newRightFormula);
        }

    }

    /**
     * Evaluates a subformula of the form "~leftFormula"
     */
    @Override
    public Formula caseNot(final Not notFormula) {

        final Position pos = this.positionStack.peek();

        final Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        final Formula newFormula = notFormula.getLeft().apply(this);

        this.positionStack.pop();

        if (newFormula instanceof FormulaTruthValue) {
            if (newFormula.equals(FormulaTruthValue.TRUE)) {
                return FormulaTruthValue.FALSE;
            } else {
                return FormulaTruthValue.TRUE;
            }
        }

        return Not.create(newFormula);
    }

    /**
     * Evaluates a subformula of the form "leftFormula \/ rightFormula"
     */
    @Override
    public Formula caseOr(final Or orFormula) {

        final Formula left = orFormula.getLeft();
        final Formula right = orFormula.getRight();

        final Position pos = this.positionStack.peek();

        final Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        final Formula newPhi = left.apply(this);

        final Position rPos = Position.create(pos);
        rPos.add(1);
        this.positionStack.push(rPos);

        final Formula newPsi = right.apply(this);

        this.positionStack.pop();

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
    public Formula caseTruthValue(final FormulaTruthValue truthValue) {
        this.positionStack.pop();
        return truthValue;
    }

    /**
     * Evaluates a term f(t_1, ... , t_n) mit a defined function symbol f
     */
    @Override
    public AlgebraTerm caseFunctionApp(final AlgebraFunctionApplication fappl) {

        if (!fappl.isMetaFunctionApplication()) {

            final Position pos = this.positionStack.peek();

            final SyntacticFunctionSymbol fsym = fappl.getFunctionSymbol();

            if (fsym.equals(this.laProgram.fsEqual)) {
                if (IsLATermVisitor.apply(fappl.getArgument(0), this.laProgram)
                    && IsLATermVisitor.apply(fappl.getArgument(1), this.laProgram)) {
                    final LinearConstraint constraint =
                        LinearConstraint.createEquation(fappl.getArgument(0), fappl.getArgument(1), this.laProgram);
                    if (constraint.getConstant().equals(Rational.zero) && constraint.getCoefficients().isEmpty()) {
                        return ConstructorApp.create(this.laProgram.csTrue);
                    }
                }
            }

            // go through all rules for this function symbol

            final Set<Rule> rulesForSymbol = this.program.getAllRules(fsym);

            if (rulesForSymbol != null) {
                nextRule: for (final Rule rule : rulesForSymbol) {

                    /* try to match lhs of a rule with term */
                    if (this.laProgram.semilaBasedFunctionSymbols.contains(fsym)) {

                        final Set<AlgebraVariable> usedVariables = fappl.getVars();

                        final Rule renamedRule = rule.replaceVariables(usedVariables);

                        final Set<AlgebraVariable> preferedVariables = renamedRule.getUsedVariables();

                        usedVariables.addAll(preferedVariables);

                        final List<AlgebraTerm> fapplArgs = fappl.getArguments();
                        final Pair<List<AlgebraTerm>, Map<AlgebraTerm, AlgebraVariable>> result =
                            FunctionAbstractionVisitor.apply(fapplArgs, usedVariables, this.program);
                        final List<AlgebraTerm> fapplAbstractedArgs = result.x;
                        final Map<AlgebraTerm, AlgebraVariable> abstraction = result.y;

                        final List<AlgebraTerm> renamedRuleLeftArgs = renamedRule.getLeft().getArguments();

                        final LASolver las = new LASolver(preferedVariables);

                        for (int i = 0; i < renamedRuleLeftArgs.size(); i++) {
                            final AlgebraTerm t = renamedRuleLeftArgs.get(i);
                            final AlgebraTerm s = fapplAbstractedArgs.get(i);

                            final LinearConstraint constraint = LinearConstraint.createEquation(t, s, this.laProgram);

                            las.addConstraint(constraint);
                        }

                        // we have to check the conditions later

                        //                        for (Rule cond : renamedRule.getConds()) {
                        //                            Term left = cond.getLeft();
                        //                            Term right = cond.getRight();
                        //
                        //                            Equation eq = Equation.create(left, right);
                        //                            LinearConstraint constraint = LinearConstraint.create(eq, laProgram);
                        //
                        //                            las.addConstraint(constraint);
                        //                        }

                        final boolean solvable = las.solve();

                        if (!solvable) {
                            // no matcher found
                            continue nextRule;
                        } else {
                            final ArrayList<LinearConstraint> remainingConstraints = las.getAllConstraints();

                            if (!remainingConstraints.isEmpty()) {
                                // there are still some constraints
                                // so we didn't find a matcher
                                continue;
                            }

                            final ArrayList<Dissolving> dissolvings = las.getDissolvings();

                            // check if we could dissolve for every variable in the lhs of the rule
                            nextVariable: for (final AlgebraVariable variable : preferedVariables) {
                                for (final Dissolving dissolving : dissolvings) {
                                    if (dissolving.getVariable().equals(variable)) {
                                        continue nextVariable;
                                    }
                                }

                                // only reachable iff there is a variable we couldn't dissolve for
                                // so we didn't find a matcher and try another rule
                                continue nextRule;
                            }

                            for (final Dissolving dissolving : dissolvings) {
                                final AlgebraVariable var = dissolving.getVariable();

                                if (!preferedVariables.contains(var)) {
                                    // it was dissolved for a variable from the term to reduce
                                    // this is not a matcher
                                    continue nextRule;
                                }
                            }

                            // construct matcher from dissolving
                            AlgebraSubstitution matcher = LinearIntegerHelper.toSubstitution(dissolvings, this.laProgram);

                            final AlgebraSubstitution undoAbstraction = AlgebraSubstitution.create();
                            final Set<Entry<AlgebraTerm, AlgebraVariable>> abstractionEntrySet = abstraction.entrySet();
                            for (final Entry<AlgebraTerm, AlgebraVariable> entry : abstractionEntrySet) {
                                final AlgebraTerm t = entry.getKey();
                                final AlgebraVariable var = entry.getValue();
                                undoAbstraction.put(var.getVariableSymbol(), t);
                            }

                            matcher = matcher.compose(undoAbstraction);

                            // check if the conditions are fullfilled
                            boolean matcherForRules = true;

                            final List<Rule> conds = renamedRule.getConds();

                            for (final Rule cond : conds) {
                                AlgebraTerm left;
                                AlgebraTerm newLeft = cond.getLeft().apply(matcher);
                                do {
                                    left = newLeft;
                                    newLeft = left.apply(this);
                                } while (!left.equals(newLeft));

                                AlgebraTerm right;
                                AlgebraTerm newRigth = cond.getRight();
                                do {
                                    right = newRigth;
                                    newRigth = right.apply(this);
                                } while (!right.equals(newRigth));

                                AlgebraSubstitution s2;
                                try {
                                    s2 = right.matches(left);
                                    matcher = matcher.compose(s2);
                                } catch (final UnificationException e) {
                                    matcherForRules = false;
                                }
                            }

                            if (!matcherForRules) {
                                final ArrayList<Equation> eqs = new ArrayList<Equation>(conds.size());

                                for (final Rule cond : conds) {
                                    final AlgebraTerm left = cond.getLeft().apply(matcher);
                                    final AlgebraTerm right = cond.getRight().apply(matcher);
                                    final Equation eq = Equation.create(left, right);
                                    eqs.add(eq);
                                }
                                final Formula condition = And.create(eqs);

                                final Formula contextFormula =
                                    ConditionalRewritingVisitor.createContextFormula(this.formula, pos);

                                Formula condCheckFormula;
                                if (contextFormula != null) {
                                    condCheckFormula = Implication.create(contextFormula, condition);
                                } else {
                                    condCheckFormula = condition;
                                }

                                // check if condCheckFormula can be evaluated to true

                                final Formula negCondCheckFormula = Not.create(condCheckFormula);

                                final Formula res =
                                    LASimplificationProcessor.simplifyWithLA(negCondCheckFormula, this.program);

                                if (!res.equals(FormulaTruthValue.FALSE)) {
                                    // we could not show a contradiction
                                    matcherForRules = false;
                                    continue nextRule;
                                }

                            }

                            final AlgebraTerm newTerm = renamedRule.getRight().apply(matcher);

                            return newTerm;

                        }

                    } else {
                        try {
                            AlgebraSubstitution matcher = rule.getLeft().matches(fappl);

                            // check if the conditions are fullfilled
                            boolean matcherForRules = true;

                            final List<Rule> conds = rule.getConds();

                            for (final Rule cond : conds) {
                                AlgebraTerm left;
                                AlgebraTerm newLeft = cond.getLeft().apply(matcher);
                                do {
                                    left = newLeft;
                                    newLeft = left.apply(this);
                                } while (!left.equals(newLeft));

                                AlgebraTerm right;
                                AlgebraTerm newRigth = cond.getRight();
                                do {
                                    right = newRigth;
                                    newRigth = right.apply(this);
                                } while (!right.equals(newRigth));

                                AlgebraSubstitution s2;
                                try {
                                    s2 = right.matches(left);
                                    matcher = matcher.compose(s2);
                                } catch (final UnificationException e) {
                                    matcherForRules = false;
                                }
                            }

                            if (!matcherForRules) {
                                // we try to find a contradiction with LA

                                final ArrayList<Equation> eqs = new ArrayList<Equation>(conds.size());

                                for (final Rule cond : conds) {
                                    final AlgebraTerm left = cond.getLeft().apply(matcher);
                                    final AlgebraTerm right = cond.getRight().apply(matcher);
                                    final Equation eq = Equation.create(left, right);
                                    eqs.add(eq);
                                }
                                final Formula condition = And.create(eqs);

                                final Formula contextFormula =
                                    ConditionalRewritingVisitor.createContextFormula(this.formula, pos);

                                Formula condCheckFormula;
                                if (contextFormula != null) {
                                    condCheckFormula = Implication.create(contextFormula, condition);
                                } else {
                                    condCheckFormula = condition;
                                }

                                // check if condCheckFormula can be evaluated to true

                                final Formula negCondCheckFormula = Not.create(condCheckFormula);

                                final Pair<List<Formula>, Formula> res =
                                    LASimplificationProcessor.laSimplify(negCondCheckFormula, this.program);
                                final List<Formula> todos = res.x;

                                if (!todos.isEmpty()) {
                                    // we could not show a contradiction
                                    continue nextRule;
                                }

                            }

                            final AlgebraTerm newTerm = rule.getRight().apply(matcher);

                            return newTerm;

                        } catch (final UnificationException e) {
                            // cannot be matched to this rule
                            // so try another rule
                        }

                    }
                }
            }

            final int size = fappl.getArguments().size();

            final List<AlgebraTerm> newArguments = new ArrayList<AlgebraTerm>(size);

            for (int i = 0; i < size; i++) {
                newArguments.add(fappl.getArgument(i).apply(this));
            }

            final AlgebraTerm newTerm = AlgebraFunctionApplication.create(fsym, newArguments);

            return newTerm;
        }

        throw new RuntimeException("Should not be applied to annotated terms");

    }

    /**
     * Returns a copy of the variable
     */
    @Override
    public AlgebraTerm caseVariable(final AlgebraVariable v) {
        return v.deepcopy();
    }
}

class FunctionAbstractionVisitor implements CoarseGrainedTermVisitor<AlgebraTerm> {

    private final Map<AlgebraTerm, AlgebraVariable> abstraction;

    private final LAProgramProperties laProgram;

    private final FreshVarGenerator fvg;

    private final AlgebraVariable abstractionVariable;

    private FunctionAbstractionVisitor(final Set<AlgebraVariable> usedVariables, final Program program) {

        // init object's variables
        this.abstraction = new HashMap<AlgebraTerm, AlgebraVariable>();
        this.laProgram = program.laProgramProperties;
        this.fvg = new FreshVarGenerator(usedVariables);

        final VariableSymbol varsymb = VariableSymbol.create("A", this.laProgram.sortNat);
        this.abstractionVariable = AlgebraVariable.create(varsymb);
    }

    public static Pair<List<AlgebraTerm>, Map<AlgebraTerm, AlgebraVariable>> apply(final List<AlgebraTerm> terms,
        final Set<AlgebraVariable> usedVariables,
        final Program program) {

        final FunctionAbstractionVisitor funcAbstrcVisitor = new FunctionAbstractionVisitor(usedVariables, program);

        final ArrayList<AlgebraTerm> newTerms = new ArrayList<AlgebraTerm>(terms.size());

        for (final AlgebraTerm term : terms) {
            final AlgebraTerm newTerm = term.apply(funcAbstrcVisitor);
            newTerms.add(newTerm);
        }

        return new Pair<List<AlgebraTerm>, Map<AlgebraTerm, AlgebraVariable>>(newTerms, funcAbstrcVisitor.abstraction);

    }

    /**
     * Evaluates a term f(t_1, ... , t_n) with a function symbol f
     *
     * If we find a term not being Zero, Succ(x) or Plus(x,y)
     * we abstract to a new variable.
     */
    @Override
    public AlgebraTerm caseFunctionApp(final AlgebraFunctionApplication fappl) {

        final SyntacticFunctionSymbol functionSymbol = fappl.getFunctionSymbol();

        if (functionSymbol.equals(this.laProgram.csZero) || functionSymbol.equals(this.laProgram.csSucc)
            || functionSymbol.equals(this.laProgram.fsPlus)) {
            // no need to abstract from symbol

            // do recursive abstraction in subterms
            final List<AlgebraTerm> newArguments = new ArrayList<AlgebraTerm>(functionSymbol.getArity());
            for (final AlgebraTerm arg : fappl.getArguments()) {
                final AlgebraTerm newArg = arg.apply(this);
                newArguments.add(newArg);
            }

            final AlgebraTerm newTerm = AlgebraFunctionApplication.create(functionSymbol, newArguments);

            return newTerm;
        } else {
            // abstract

            // check if we have done this abstraction already
            AlgebraVariable var = this.abstraction.get(fappl);
            if (var == null) {
                var = this.fvg.getFreshVariable(this.abstractionVariable, false);

                // remeber the abstraction made
                this.abstraction.put(fappl, var);
            }

            return var;
        }

    }

    /**
     * Returns a copy of the variable
     */
    @Override
    public AlgebraTerm caseVariable(final AlgebraVariable v) {
        return v.deepcopy();
    }
}
