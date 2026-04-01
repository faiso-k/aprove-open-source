package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Implication;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * Abstracts from uninterpreted function symbols,
 * transforms the formula into its dnf,
 * simplifies all conjunctions using the LA Solver (LAIntegerConstraintSimplifier)
 * and finally undos the abstraction.
 *
 * However at the end the resulting formula is in dnf.
 *
 * Mostly you want to call an indirect proof before
 * so that you can show the unsatisfybility.
 *
 * @author dickmeis
 * @version $Id$
 *
 */
@NoParams
public class LASimplificationProcessor extends TheoremProverProcessor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {

            TheoremProverObligation theorem_obl = (TheoremProverObligation) obl;

            // only for indirect proofs
            if(theorem_obl.isIndirectProof()) {
                return true;
            }
        }
        return false;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        Formula formula = obligationInput.getFormula();

        Program program = obligationInput.getProgram();

        Pair<List<Formula>, Formula> res = LASimplificationProcessor.laSimplify(formula, program);
        List<Formula> newConjunctions = res.x;
        Formula dnfFormula = res.y;

        if(newConjunctions.contains(FormulaTruthValue.TRUE)){
            LASimplificationProof proof = new LASimplificationProof(dnfFormula);
            return ResultFactory.proved(proof);
        }

        // build new formula
        if(newConjunctions.isEmpty()){
            return ResultFactory.disproved(
                    new LASimplificationProof(dnfFormula));
        }

        int size = newConjunctions.size();
        if(size == 1){
            Formula newFormula = newConjunctions.get(0);

            if(formula.equals(newFormula)){
                return ResultFactory.unsuccessful();
            }

            TheoremProverObligation newObligation = new TheoremProverObligation(newFormula, obligationInput);

            return ResultFactory.proved(newObligation,
                    YNMImplication.EQUIVALENT,
                    new LASimplificationProof(dnfFormula, newObligation));
        }

        ArrayList<TheoremProverObligation> todos = new ArrayList<TheoremProverObligation>(size);
        for(int i = 0; i < size; i++){
            Formula newFormula = newConjunctions.get(i);
            TheoremProverObligation newObligation = new TheoremProverObligation(newFormula, obligationInput);
            todos.add(newObligation);
        }

        return ResultFactory.provedOr(todos ,
                YNMImplication.EQUIVALENT,
                new LASimplificationProof(dnfFormula, todos));

    }

    /**
     * Simplifies a given formula.
     * First the formula gets transformed into dnf.
     * The each conjunction is simplified
     * The result of the simplification is a list of remaining subgoals.
     * Additionally, for information purpose the dnf formula is given back, too.
     *
     * @param formula The formula to simplify
     * @param program background information
     * @return a pair consisting of the remaining subgoals and the dnf formula
     */
    public static Pair<List<Formula>,Formula> laSimplify(Formula formula, Program program){
        Set<AlgebraVariable> usedVariables = formula.getAllVariables();

        Formula dnfFormula = ToDNFTransformerVisitor.apply(formula);

        List<Formula> allConjunctions = GetAllConjunctionsFromDNFVisitor.apply(dnfFormula);
        List<Formula> newConjunctions = new ArrayList<Formula>(allConjunctions.size());

        // simplify all conjunctions
        for (Formula conjunction : allConjunctions) {

            Formula resFormula = SimplificationWithFunctionAbstraction.apply(conjunction, usedVariables, program);

            if(!resFormula.equals(FormulaTruthValue.FALSE)){
                newConjunctions.add(resFormula);
            }

        }

        return new Pair<List<Formula>, Formula>(newConjunctions, dnfFormula);
    }

    public static Formula simplifyWithLA(Formula formula, Program program){
        Pair<List<Formula>, Formula> res = LASimplificationProcessor.laSimplify(formula, program);
        List<Formula> newConjunctions = res.x;

        if(newConjunctions.contains(FormulaTruthValue.TRUE)){
            return FormulaTruthValue.TRUE;
        }

        // remove all false
        for (Iterator iter = newConjunctions.iterator(); iter.hasNext();) {
            Formula f = (Formula) iter.next();
            if(f.equals(FormulaTruthValue.FALSE)){
                iter.remove();
            }
        }

        // build new formula
        if(newConjunctions.isEmpty()){
            return FormulaTruthValue.FALSE;
        }
        else{
            Formula or = Or.create(newConjunctions);
            return or;
        }
    }

}


/**
 * Traverses a conjunction and abstracts from uninterpreted function applications for Nat
 * by replacing them with variables.
 * At the same time the LA solver gets configured
 * with the obtained LA constraints.
 */
class SimplificationWithFunctionAbstraction implements FineFormulaVisitor<Object>,
        CoarseGrainedTermVisitor<AlgebraTerm> {

    private Map<AlgebraTerm, AlgebraVariable> abstraction;

    private LASolver lasolver;

    private List<Formula> literals;

    private LAProgramProperties laProgram;

    private boolean not;

    private FreshVarGenerator fvg;

    private AlgebraVariable abstractionVariable;

    private int doAbstraction;


    private SimplificationWithFunctionAbstraction(Set<AlgebraVariable> usedVariables, Program program) {

        // init object's variables
        this.abstraction = new HashMap<AlgebraTerm, AlgebraVariable>();
        this.literals = new ArrayList<Formula>();
        this.lasolver = new LASolver();
        this.laProgram = program.laProgramProperties;
        this.not = false;
        this.fvg = new FreshVarGenerator(usedVariables);
        VariableSymbol varsymb = VariableSymbol.create("A", this.laProgram.sortNat);
        this.abstractionVariable = AlgebraVariable.create(varsymb);
        this.doAbstraction = 0;
    }

    public static Formula apply(Formula formula, Set<AlgebraVariable> usedVariables, Program program) {

        SimplificationWithFunctionAbstraction funcAbstrcVisitor = new SimplificationWithFunctionAbstraction(
                usedVariables, program);

        formula.apply(funcAbstrcVisitor);

        boolean solvable = funcAbstrcVisitor.lasolver.solve();

        if (!solvable){
            return FormulaTruthValue.FALSE;
        }

        // construct the substitution to undo the abstraction
        AlgebraSubstitution reverseAbstraction = AlgebraSubstitution.create();
        for (Entry<AlgebraTerm, AlgebraVariable> entry : funcAbstrcVisitor.abstraction.entrySet()) {
            reverseAbstraction.put(entry.getValue().getVariableSymbol(), entry.getKey());
        }

        ArrayList<Dissolving> dissolvings = funcAbstrcVisitor.lasolver.getDissolvings();
        ArrayList<LinearConstraint> constraints = funcAbstrcVisitor.lasolver.getConstraints();
        ArrayList<LinearConstraint> inequations = funcAbstrcVisitor.lasolver.getInequations();
        ArrayList<LinearConstraint> equationsLA = funcAbstrcVisitor.lasolver.getEquations();

        ArrayList<Equation> eqLits = new ArrayList<Equation>(dissolvings.size()
                + equationsLA.size());

        ArrayList<Formula> resLiterals = new ArrayList<Formula>(constraints.size()
                + inequations.size() + eqLits.size() + funcAbstrcVisitor.literals.size());

        /*
         * To build the new formula it was found that
         * the order of dissolvings, other literals and simplified literals
         * reaches the fix point of the reapeated application of the
         * la simplification processor more quickly
         */

        // construct equations from the dissolving
        for (Dissolving dissolving : dissolvings) {
            AlgebraVariable var = dissolving.getVariable();
            AlgebraTerm rhs = dissolving.rhsToTerm(program.laProgramProperties);

            AlgebraTerm lhs = var.apply(reverseAbstraction);

            Equation lit = Equation.create(lhs, rhs);

            // is needed for the e-tecton2 example
            for (Equation eq : eqLits) {
                AlgebraTerm left = eq.getLeft();
                AlgebraTerm right = eq.getRight();

                lit = (Equation) lit.replaceTermByTerm(left, right);
            }

            eqLits.add(lit);
            resLiterals.add(lit);
        }

        for (LinearConstraint eq : equationsLA) {
            Equation lit = LinearIntegerHelper.toEquation(eq, program.laProgramProperties);

            lit = (Equation) lit.apply(reverseAbstraction);

//            for (Equation eqL : eqLits) {
//                Term left = eqL.getLeft();
//                Term right = eqL.getRight();
//
//                lit = (Equation) lit.replaceTermByTerm(left, right);
//            }

            eqLits.add(lit);
            resLiterals.add(lit);
        }

        // apply insert all equations in the other literals
        for (Formula literal : funcAbstrcVisitor.literals) {
            Formula newLit = literal;

            for (Equation eq : eqLits) {
                AlgebraTerm left = eq.getLeft();
                AlgebraTerm right = eq.getRight();

                newLit = newLit.replaceTermByTerm(left, right);
            }

            resLiterals.add(newLit);
        }

        // construct terms / equations for the <= LA constraints
        for (LinearConstraint constraint : constraints) {
            Formula lit = LinearIntegerHelper.toEquation(constraint, program.laProgramProperties);

            lit = lit.apply(reverseAbstraction);

            for (Equation eq : eqLits) {
                AlgebraTerm left = eq.getLeft();
                AlgebraTerm right = eq.getRight();

                lit = lit.replaceTermByTerm(left, right);
            }

            resLiterals.add(lit);
        }

        // construct terms / equations for the inequalities
        for (LinearConstraint constraint : inequations) {
            Formula lit = LinearIntegerHelper.toEquation(constraint, program.laProgramProperties);

            lit = lit.apply(reverseAbstraction);

            for (Equation eq : eqLits) {
                AlgebraTerm left = eq.getLeft();
                AlgebraTerm right = eq.getRight();

                lit = lit.replaceTermByTerm(left, right);
            }

            resLiterals.add(lit);
        }

        Formula newFormula;

        if(!resLiterals.isEmpty()){
             newFormula = And.create(resLiterals);
        }
        else{
            newFormula = FormulaTruthValue.TRUE;
        }

        return newFormula;

    }


    /**
     * Evaluates a subformula of the form "leftFormula /\ rightFormula"
     *
     * just descend
     */
    @Override
    public Object caseAnd(And and) {

        Formula left = and.getLeft();
        Formula right = and.getRight();

        left.apply(this);
        right.apply(this);

        return null;
    }

    /**
     * Evaluates a subformula of the form "leftTerm = rightTerm"
     *
     * When this is an equation of two Nats
     * we start doing the abstraction.
     */
    @Override
    public Object caseEquation(Equation phi) {

        AlgebraTerm left = phi.getLeft();
        AlgebraTerm right = phi.getRight();

        // abstract when within an LA equation
        if (left.getSort().equals(this.laProgram.sortNat)){
            this.doAbstraction++;
        }

        AlgebraTerm newLeft = left.apply(this);
        AlgebraTerm newRight = right.apply(this);

        if (left.getSort().equals(this.laProgram.sortNat)){
            this.doAbstraction--;
        }

        Formula lit = Equation.create(newLeft, newRight);

        LinearConstraint constraint = LinearConstraint.create((Equation) lit, this.laProgram);

        if(constraint == null){
            // an error occured
            // so this equation is not LA
            // and we treat it like an literal but do not consider it for simplification

            if(this.not){
                lit = Not.create(lit);
            }
            this.literals.add(lit);
        }
        else{
            if(this.not){
                constraint = constraint.negate();
            }
            this.lasolver.addConstraint(constraint);
        }

        return null;
    }

    /**
     * Evaluates a subformula of the form "leftFormula <-> rightFormula"
     *
     * ERROR
     */
    @Override
    public Formula caseEquivalence(Equivalence equiv) {

        throw new RuntimeException("There is an equivalence in a DNF");
    }

    /**
     * Evaluates a subformula of the form "leftFormula -> rightFormula"
     *
     * ERROR
     */
    @Override
    public Object caseImplication(Implication implication) {

        throw new RuntimeException("There is an implication in a DNF");
    }

    /**
     * Evaluates a subformula of the form "~leftFormula"
     *
     * save that we are in a negative literal and descend
     */
    @Override
    public Object caseNot(Not notFormula) {
        // because of the transformation we do not have axpressions like ~ ~ A
        // there is maximal one negation

        this.not = true;

        notFormula.getLeft().apply(this);

        this.not = false;

        return null;

    }

    /**
     * Evaluates a subformula of the form "leftFormula \/ rightFormula"
     *
     * ERROR
     */
    @Override
    public Object caseOr(Or or) {

        throw new RuntimeException("There is an or deep inside a DNF");
    }

    /**
     * Evaluates a Truthvalue.
     *
     * This is unlikely to happen, normally it gets handeled by symbolic evaluation already before.
     *
     * A truth value gets transformed in the case of TRUE into a tautology (0=0)
     * and in the case of FALSE into a contradiction (0!=0).
     */
    @Override
    public Object caseTruthValue(FormulaTruthValue truthValue) {

        // 0 = 0
        LinearConstraint constraint = new LinearConstraint(
                new HashMap<AlgebraVariable, Rational>(),
                ConstraintType.EQUALITY,
                Rational.zero);

        if(truthValue.equals(FormulaTruthValue.FALSE)){
            constraint = constraint.negate();
        }

        if(this.not){
            constraint = constraint.negate();
        }
        this.lasolver.addConstraint(constraint);

        return null;
    }

    /**
     * Evaluates a term f(t_1, ... , t_n) with a function symbol f
     *
     * If we find an LA function symbol we start doing the abstraction on its arguments.
     */
    @Override
    public AlgebraTerm caseFunctionApp(AlgebraFunctionApplication fappl) {

        SyntacticFunctionSymbol functionSymbol = fappl.getFunctionSymbol();

        if(functionSymbol.equals(this.laProgram.csZero) ||
                functionSymbol.equals(this.laProgram.csSucc) ||
                functionSymbol.equals(this.laProgram.fsPlus) ||
                functionSymbol.equals(this.laProgram.fsEqual)||
                functionSymbol.equals(this.laProgram.fsLesseq)||
                functionSymbol.equals(this.laProgram.fsLess)||
                functionSymbol.equals(this.laProgram.fsInequal)||
                functionSymbol.equals(this.laProgram.fsGreater)||
                functionSymbol.equals(this.laProgram.fsGreatereq)){

            // abstract when within an LA function

            this.doAbstraction++;

            // try form left to right
            List<AlgebraTerm> newArguments = new ArrayList<AlgebraTerm>(functionSymbol.getArity());
            for (AlgebraTerm arg : fappl.getArguments()) {
                AlgebraTerm newArg = arg.apply(this);
                newArguments.add(newArg);
            }

            this.doAbstraction--;

            AlgebraTerm newTerm = AlgebraFunctionApplication.create(functionSymbol,
                    newArguments);
            return newTerm;
        }

        if(this.doAbstraction > 0){

            // check if we have done this abstraction already
            AlgebraVariable var = this.abstraction.get(fappl);
            if(var == null){
                var = this.fvg.getFreshVariable(this.abstractionVariable, false);

                // remeber the abstraction made
                this.abstraction.put(fappl, var);
            }

            return var;
        }

        return fappl;

    }

    /**
     * Returns a copy of the variable
     */
    @Override
    public AlgebraTerm caseVariable(AlgebraVariable v) {
        return v.shallowcopy();
    }
}
