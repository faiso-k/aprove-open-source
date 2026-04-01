package aprove.verification.oldframework.Logic.Formulas.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Exceptions.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Searches for positions where we can do conditional(!) rewriting.
 * If such a position is found a pair is constructed.
 * The first component are conditions which have to be fullfilled so that the conditional rewrite step can be perform.
 * The second component would be the result of the conditional rewrite step.
 *
 * When the conditions get check they will be implicitly all quantified.
 * Actually, we would suffy to find only one solution because for rewriting we are looking for a matcher.
 * But this matching problem could not be solved by symbolic evaluation.
 *
 * @author dickmeis
 * @version $Id$
 */

public class ConditionalRewritingVisitor implements
        CoarseFormulaVisitor<Object>, CoarseGrainedTermVisitor<AlgebraTerm> {

    protected Program program;

    private Stack<Position> positionStack;

    private List<RewriteApplication> applications;

    public static List<Pair<Formula, Formula>> apply(Formula formula, Program program) {

        ConditionalRewritingVisitor condRewVisitor = new ConditionalRewritingVisitor(
                program);

        formula.apply(condRewVisitor);

        if (condRewVisitor.applications.isEmpty()) {
            return null;
        }

        List<Pair<Formula, Formula>> newFormulas = new ArrayList<Pair<Formula, Formula>>(
                condRewVisitor.applications.size());

        Formula contextFormula;
        try {
            for (RewriteApplication appl : condRewVisitor.applications) {

                contextFormula = ConditionalRewritingVisitor.createContextFormula(formula, appl.position);

                Formula condCheckFormula;
                if (contextFormula != null) {
                    condCheckFormula = Implication.create(contextFormula,
                            appl.condition);
                }
                else {
                    condCheckFormula = appl.condition;
                }

                Formula newFormula = formula.replaceTermAt(appl.rhs,
                        appl.position);

                Pair<Formula, Formula> p = new Pair<Formula, Formula>(
                        condCheckFormula, newFormula);

                newFormulas.add(p);
            }
        }
        catch (InvalidPositionException e) {
            e.printStackTrace();
        }

        return newFormulas;
    }

    /**
     * Create the context of the position of a formula for the condition to
     * proof
     *
     * @param formula
     *            The formula from which the context is extracted.
     * @param position
     *            The position for which the context is created.
     * @return the context
     */
    public static Formula createContextFormula(Formula formula,
            Position position) {

        try {
            // mark the equation where the rewriting has taken place
            EquationMarkerVisitor equationMarkerVisitor = new EquationMarkerVisitor(
                    position);

            Formula markedFormula = formula.deepcopy();

            markedFormula.apply(equationMarkerVisitor);

            // transform to dnf
            Formula dnfFormula = ToDNFTransformerVisitor.apply(markedFormula);

            BuildContextFromDNFVisitor contextBuilder = new BuildContextFromDNFVisitor();

            Formula contextFormula = dnfFormula.apply(contextBuilder);

            return contextFormula;
        }
        catch (Exception e) {
            e.printStackTrace();
        }

        return null;
    }

    protected ConditionalRewritingVisitor(Program program) {

        // init object's variables
        this.program = program;

        this.positionStack = new Stack<Position>();
        this.positionStack.push(Position.create());

        this.applications = new ArrayList<RewriteApplication>();
    }

    /**
     * Evaluates a subformula of the form "leftTerm = rightTerm"
     */
    @Override
    public Object caseEquation(Equation phi) {

        AlgebraTerm left = phi.getLeft();
        AlgebraTerm right = phi.getRight();

        Position pos = this.positionStack.peek();

        Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        left.apply(this);

        Position rPos = Position.create(pos);
        rPos.add(1);
        this.positionStack.push(rPos);

        right.apply(this);

        this.positionStack.pop();
        return null;
    }

    @Override
    public Object caseJunctorFormula(JunctorFormula jFormula) {

        Formula left = jFormula.getLeft();
        Formula right = jFormula.getRight();

        Position pos = this.positionStack.peek();

        Position lPos = Position.create(pos);
        lPos.add(0);
        this.positionStack.push(lPos);

        left.apply(this);

        /*
         * right == null in the case of a Not formula
         */
        if (right != null) {
            Position rPos = Position.create(pos);
            rPos.add(1);
            this.positionStack.push(rPos);

            right.apply(this);
        }

        this.positionStack.pop();

        return null;

    }

    @Override
    public Object caseTruthValue(FormulaTruthValue truthval) {
        this.positionStack.pop();
        return null;
    }

    /**
     * Evaluates a term f(t_1, ... , t_n) with a function symbol f
     *
     * Try all matching left hand sides
     */
    @Override
    public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication fappl) {

        if (!fappl.isMetaFunctionApplication()) {

            SyntacticFunctionSymbol functionSymbol = fappl.getFunctionSymbol();

            Position pos = this.positionStack.peek();

            // go through all rules for this function symbol

            Set<Rule> rulesForSymbol = this.program.getAllRules(functionSymbol);

            if (rulesForSymbol != null) {
                for (Rule rule : rulesForSymbol) {

                    /* try to match lhs of a rule with term */
                    try {
                        List<Rule> conds = rule.getConds();
                        int condSize = conds.size();

                        if (condSize == 0) {
                            // not a conditional rule
                            continue;
                        }

                        AlgebraSubstitution subs = rule.getLeft().matches(fappl);
                        ArrayList<Equation> eqs = new ArrayList<Equation>(
                                condSize);

                        for (Rule cond : conds) {
                            AlgebraTerm left = cond.getLeft().apply(subs);
                            AlgebraTerm right = cond.getRight().apply(subs);
                            Equation eq = Equation.create(left, right);
                            eqs.add(eq);
                        }
                        Formula condition = And.create(eqs);
                        AlgebraTerm right = rule.getRight().apply(subs);
                        RewriteApplication rw = new RewriteApplication(
                                functionSymbol, pos, condition, right);
                        this.applications.add(rw);
                    }
                    catch (UnificationException e) {
                        // cannot be matched to this rule
                        // so try another rule
                    }
                }
            }

            int size = functionSymbol.getArity();

            // try form left to right
            for (int i = 0; i < size; i++) {
                Position iPos = Position.create(pos);
                iPos.add(i);
                this.positionStack.push(iPos);

                AlgebraTerm arg = fappl.getArgument(i);
                arg.apply(this);
            }

            this.positionStack.pop();

            return null;
        }

        throw new RuntimeException("Should not be applied to annotated terms");
    }

    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        return null;
    }

}

/**
 * Just a record to store some information
 */
class RewriteApplication {

    // just for better debugging
    SyntacticFunctionSymbol functSymbol;

    Position position;

    Formula condition;

    AlgebraTerm rhs;

    RewriteApplication(SyntacticFunctionSymbol functSymbol, Position position,
            Formula condition, AlgebraTerm rhs) {
        this.functSymbol = functSymbol;
        this.position = position;
        this.condition = condition;
        this.rhs = rhs;
    }
}

/**
 * Trafers a formula to the equation having the term at the position as subterm
 */
class EquationMarkerVisitor implements CoarseFormulaVisitorException<Equation> {

    private Position position;

    private Position position_backup;

    /**
     * @param position
     *            The position where there is the term being a subterm of the
     *            equation be marked
     */
    public EquationMarkerVisitor(Position position) {
        this.position = position.deepcopy();
        this.position_backup = position.deepcopy();
    }

    /**
     * Marks the reached equation
     */
    @Override
    public Equation caseEquation(Equation phi) {

        phi.setFlag(true);

        return phi;
    }

    /**
     * Evaluates a truthvalue.
     *
     * @throws InvalidPositionException
     */
    @Override
    public Equation caseTruthValue(FormulaTruthValue truthvalFormula)
            throws InvalidPositionException {

        throw new InvalidPositionException(this.position_backup,
                "Not the position of a term in an equation");

    }

    /**
     * Depending on the position either goes left or right
     * @throws InvalidPositionException
     */
    @Override
    public Equation caseJunctorFormula(JunctorFormula jFormula)
            throws InvalidPositionException {

        int p = this.position.remove(0);

        if (p == 0) {
            return jFormula.getLeft().apply(this);
        }
        else if (p == 1) {
            if (jFormula instanceof Not) {
                throw new InvalidPositionException(this.position_backup,
                        "Not the position of a subformula");
            }

            return jFormula.getRight().apply(this);
        }
        else {
            throw new InvalidPositionException(this.position_backup,
                    "Not the position of a subformula");
        }
    }

}

/**
 * Transforms a formula with a marked equation into a formula being the context
 * for this
 */
class BuildContextFromDNFVisitor implements FineFormulaVisitor<Formula> {

    private boolean found = false;

    /**
     * Evaluates a subformula of the form "leftFormula /\ rightFormula"
     *
     * Mostly just descents. But if beneath there was a literal removed because
     * it was marked only the other side is returned.
     */
    @Override
    public Formula caseAnd(And andFormula) {
        Formula left = andFormula.getLeft();
        Formula right = andFormula.getRight();

        Formula newLeft = left.apply(this);

        if (newLeft == null) {
            return right.deepcopy();
        }

        Formula newRight = right.apply(this);
        if (newRight == null) {
            return newLeft;
        }

        Formula and = And.create(newLeft, newRight);

        return and;
    }

    /**
     * If the equation is marked, it is not returned but the mark is removed.
     */
    @Override
    public Formula caseEquation(Equation phi) {

        if (phi.getFlag()) {
            phi.setFlag(false);
            this.found = true;
            return null;
        }
        else {
            return phi.deepcopy();
        }
    }

    /**
     * Evaluates a subformula of the form "leftFormula <--> rightFormula"
     *
     * ERROR
     */
    @Override
    public Formula caseEquivalence(Equivalence equivFormula) {

        throw new RuntimeException(
                "Transformation to literals was not correct.");
    }

    /**
     * Evaluates a subformula of the form "leftFormula --> rightFormula"
     *
     * ERROR
     */
    @Override
    public Formula caseImplication(Implication implFormula) {

        throw new RuntimeException(
                "Transformation to literals was not correct.");
    }

    /**
     * Evaluates a subformula of the form "~ formula"
     *
     * Mostly just descents. But if beneath there was an equation removed
     * because it was marked null is returned.
     */
    @Override
    public Formula caseNot(Not notFormula) {
        Formula newLeft = notFormula.getLeft().apply(this);
        if (newLeft == null) {
            return null;
        }
        else {
            return Not.create(newLeft);
        }
    }

    /**
     * Evaluates a subformula of the form "leftFormula \/ rightFormula"
     *
     * If a subformula contains the mark, the other is negated and the
     * conjunction is returned.
     */
    @Override
    public Formula caseOr(Or orFormula) {
        Formula left = orFormula.getLeft();
        Formula right = orFormula.getRight();

        Formula newLeft = left.apply(this);
        if (this.found) {
            Formula not = Not.create(right.deepcopy());

            if (newLeft == null) {
                return not;
            }

            And and = And.create(newLeft, not);

            return and;
        }
        Formula newRight = right.apply(this);
        if (this.found) {
            Formula not = Not.create(newLeft);

            if (newRight == null) {
                return not;
            }

            And and = And.create(not, newRight);

            return and;
        }

        Or or = Or.create(newLeft, newRight);

        return or;
    }

    /**
     * Evaluates a truthvalue.
     *
     * This is unlikely to happen, normally it gets handeled by symbolic
     * evaluation already before.
     */
    @Override
    public Formula caseTruthValue(FormulaTruthValue truthvalFormula) {

        return truthvalFormula.deepcopy();
    }

}
