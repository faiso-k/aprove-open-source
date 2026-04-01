package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LemmaDatabase.*;
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
import aprove.verification.theoremprover.TheoremProverProofs.*;

/**
 * Processor that searches the lemma data base if there are lemmas concerning linear arithmetic
 * which have the same uninterpreted function symbols in common with the formula which is to
 * prove and would eliminate a term in the formula.
 *
 * @author dickmeis
 * @version $Id$
 */
@NoParams
public class LALemmaInsertionProcessor extends TheoremProverProcessor {

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof TheoremProverObligation) {
            // only for indirect proofs
            TheoremProverObligation theorem_obl = (TheoremProverObligation) obl;
            return theorem_obl.isIndirectProof();
        }
        return false;
    }

    @Override
    protected Result process(TheoremProverObligation obligationInput,
            BasicObligationNode obligationNode, Abortion aborter,
            RuntimeInformation rti) throws AbortionException {

        Program program = obligationInput.getProgram();
        LAProgramProperties laProgram = program.laProgramProperties;

        Formula formula = obligationInput.getFormula();
        Set<AlgebraVariable> usedVariables = formula.getAllVariables();

        LemmaDatabase ldb = LemmaDatabaseFactory.getLemmmaDatabase();

        Set<Equation> lemmaEquations = ldb.getAllEquations();

        Set<Formula> lemmas = ldb.retrieveAllFormulas();
        ArrayList<LAAbstractionResult> lemmata_abstraction = new ArrayList<LAAbstractionResult>(lemmas.size());
        for (Formula lemma : lemmas) {

            Formula renamedLemma = lemma.deepcopy();
            renamedLemma.renameAllVars(usedVariables);

            usedVariables.addAll(renamedLemma.getAllVariables());

            List<Formula> newLemmas = LemmaConverter.apply(renamedLemma);

            for (Formula newLemma : newLemmas) {
                // because of LemmaConverter newLemma is either an equation
                // or an implication with an equation as rhs

                Equation equation;

                if (newLemma instanceof Equation) {
                    equation = (Equation) newLemma;
                }
                else if (newLemma instanceof Implication){
                    Implication impl  = (Implication) newLemma;
                    Formula right = impl.getRight();
                    if (right instanceof Equation) {
                        equation = (Equation) right;
                    }
                    else{
                        System.err.println("something gone wrong in LemmaConverter");
                        continue;
                    }
                }
                else{
                    System.err.println("something gone wrong in LemmaConverter");
                    continue;
                }

                LAAbstractionResult res = LALemmaAbstractionVisitor.apply(equation, usedVariables, program);
                if(!res.laConstraints.isEmpty()){
                    LinearConstraint constraint = res.laConstraints.get(0);
                    if(!constraint.getConstraintType().equals(ConstraintType.INEQUALITY)){
                        // don't handle !=
                        res.original = newLemma;
                    }
                }

                if (newLemma instanceof Implication){
                    Implication impl  = (Implication) newLemma;
                    Formula left = impl.getLeft();
                    res.premise = left.deepcopy();
                }

                lemmata_abstraction.add(res);
            }
        }

        List<LALemmaInsertionProof> proofs = new ArrayList<LALemmaInsertionProof>();

        Formula dnfFormula = ToDNFTransformerVisitor.apply(formula);
        List<Formula> allConjunctions = GetAllConjunctionsFromDNFVisitor.apply(dnfFormula);

        // work on all conjunctions
        for (int c = 0; c < allConjunctions.size(); c++) {
            Formula conjunction = allConjunctions.get(c);
            LAAbstractionResult res = LALemmaAbstractionVisitor.apply(conjunction, usedVariables, program);

            // if there is for some constraint
            for (int i = 0; i < res.laConstraints.size(); i++) {
                LinearConstraint constraint = res.laConstraints.get(i);
                Equation constraintFormula = (Equation) LinearIntegerHelper.toEquation(constraint, laProgram).apply(res.reverseAbstraction);

                Set<Entry<AlgebraVariable, Rational>> constraintEntrySet = constraint.getCoefficients().entrySet();

                // some multiplicant such that
                for (Entry<AlgebraVariable, Rational> constraintEntry : constraintEntrySet) {
                    AlgebraTerm constraintMultiplicant = constraintEntry.getKey().apply(res.reverseAbstraction);

                    // there is an equational LA lemma
                    for(int l=0; l < lemmata_abstraction.size(); l++){
                        LAAbstractionResult eq_lemma_abstraction = lemmata_abstraction.get(l);
                        if(eq_lemma_abstraction.laConstraints.isEmpty()){
                            continue;
                        }
                        LinearConstraint lemmaConstraint = eq_lemma_abstraction.laConstraints.get(0); // as we are dealing with equations there is exactly one
                        Set<Entry<AlgebraVariable, Rational>> lemmaEntrySet = lemmaConstraint.getCoefficients().entrySet();

                        // with a multiplicant
                        for (Entry<AlgebraVariable, Rational> lemmaEntry : lemmaEntrySet) {
                            AlgebraTerm lemmaMultiplicant = lemmaEntry.getKey().apply(eq_lemma_abstraction.reverseAbstraction);
                            // that matches the constraintMultiplicant
                            try {
                                AlgebraSubstitution sigma = lemmaMultiplicant.matches(constraintMultiplicant);
                                // and can be eliminated
                                Rational constraintCoeff = constraintEntry.getValue();
                                Rational lemmaCoeff = lemmaEntry.getValue();
                                if(constraintCoeff.isPositive() ^     //XOR
                                        lemmaCoeff.isPositive()){
                                    if(constraintCoeff.isPositive()){
                                        lemmaCoeff = lemmaCoeff.negate();
                                    }
                                    else{
                                        constraintCoeff = constraintCoeff.negate();
                                    }

                                    Formula originallemma = eq_lemma_abstraction.original;
                                    Formula lemma = LinearIntegerHelper.toEquation(lemmaConstraint, laProgram).apply(eq_lemma_abstraction.reverseAbstraction);

                                    Set<Entry<AlgebraTerm, AlgebraVariable>> resAbstractionEntrySet = res.abstraction.entrySet();
                                    Map<AlgebraTerm, AlgebraVariable> resAbstractionForReuse = new HashMap<AlgebraTerm, AlgebraVariable>(resAbstractionEntrySet.size());
                                    for (Entry<AlgebraTerm, AlgebraVariable> entry : resAbstractionEntrySet) {
                                        resAbstractionForReuse.put(entry.getKey(), entry.getValue());
                                        usedVariables.add(entry.getValue());
                                    }

                                    Formula specialisedLemmaEq = lemma.apply(sigma);
                                    LAAbstractionResult specLemRes = LALemmaAbstractionVisitor.apply(specialisedLemmaEq, usedVariables, resAbstractionForReuse, program);

                                    LinearConstraint constraint_mult = constraint.scalarMultiply(lemmaCoeff);
                                    LinearConstraint specLemConstraint_mult = specLemRes.laConstraints.get(0).scalarMultiply(constraintCoeff);

                                    LinearConstraint newConstraint = constraint_mult.addConstraint(specLemConstraint_mult);


                                    // and fullfills the premis of the implication lemma

                                    List<Formula> context = new ArrayList<Formula>(res.laConstraints.size());
                                    for (int i_prime = 0; i_prime < res.laConstraints.size(); i_prime++) {
                                        if(i != i_prime){
                                            // old part
                                            LinearConstraint oldAbstractLAConstraint = res.laConstraints.get(i_prime).deepcopy();
                                            Equation oldAbstractLAConstraintFormula = LinearIntegerHelper.toEquation(oldAbstractLAConstraint, laProgram);
                                            Formula oldLAConstraintFormula = oldAbstractLAConstraintFormula.apply(specLemRes.reverseAbstraction);
                                            context .add(oldLAConstraintFormula);
                                        }
                                    }

                                    Formula specLemmaPremise = eq_lemma_abstraction.premise.apply(sigma);

                                    Formula specLemma;
                                    if (specLemmaPremise.equals(FormulaTruthValue.TRUE)){
                                        specLemma = specialisedLemmaEq;
                                    }
                                    else{
                                        specLemma = Implication.create(specLemmaPremise, specialisedLemmaEq);
                                    }

                                    boolean proved = false;

                                    // don't forget the remaining literals which are not la
                                    for (Formula remLit : res.remainingLiterals) {
                                        if(remLit.equals(specLemmaPremise)){
                                            // if there is a literal which is syntactical equal to the premise it is fullfilled
                                            proved = true;
                                            break;
                                        }

                                        context.add(remLit);
                                    }

                                    if(!proved){
                                        // if we haven't already proved the premise we searche the lemma database
                                        // for an instance of the premise
                                        // this is for some examples necessary
                                        for (Equation equation : lemmaEquations) {
                                            AlgebraSubstitution matcher = equation.matches(specLemmaPremise);
                                            if (matcher != null){
                                                proved = true;
                                            }
                                        }
                                    }

                                    if(!proved){
                                        // if we still haven't proved the premise we try LA simplification

                                        // TODO better context creation as in conditional rewriting
                                        // however this was not necessary the examples

                                        Formula contextFormula = And.create(context);

                                        Formula conditionCheck;
                                        if(contextFormula != null){
                                            conditionCheck = Implication.create(contextFormula, specLemmaPremise);
                                        }
                                        else{
                                            conditionCheck = specLemmaPremise;
                                        }
                                        Formula negConditionCheck = Not.create(conditionCheck);

                                        Formula simplificationRes = LASimplificationProcessor.simplifyWithLA(negConditionCheck, program);

                                        if(! simplificationRes.equals(FormulaTruthValue.FALSE)){
                                            // we didn't got to show a contradiction in the negation
                                            // the condition may not be fullfilled
                                            // we have to try something else
                                            continue;
                                        }
                                        else{
                                            proved = true;
                                        }
                                    }

                                    // construct the new formula
                                    List<Formula> newAllConjunctions = new ArrayList<Formula>(allConjunctions.size());

                                    for (int c_prime = 0; c_prime < allConjunctions.size(); c_prime++) {
                                        if(c != c_prime){
                                            // old part
                                            newAllConjunctions.add(allConjunctions.get(c_prime).deepcopy());
                                        }
                                        else{
                                            // changed part
                                            List<Formula> newLaConstraints = new ArrayList<Formula>(res.laConstraints.size());

                                            for (int i_prime = 0; i_prime < res.laConstraints.size(); i_prime++) {
                                                if(i != i_prime){
                                                    // old part
                                                    LinearConstraint oldAbstractLAConstraint = res.laConstraints.get(i_prime).deepcopy();
                                                    Equation oldAbstractLAConstraintFormula = LinearIntegerHelper.toEquation(oldAbstractLAConstraint, laProgram);
                                                    Formula oldLAConstraintFormula = oldAbstractLAConstraintFormula.apply(specLemRes.reverseAbstraction);
                                                    newLaConstraints.add(oldLAConstraintFormula);
                                                }
                                                else{
                                                    // insert new constraint
                                                    Equation newAbstractLAConstraintFormula = LinearIntegerHelper.toEquation(newConstraint, laProgram);
                                                    Formula newLAConstraintFormula = newAbstractLAConstraintFormula.apply(specLemRes.reverseAbstraction);
                                                    newLaConstraints.add(newLAConstraintFormula);
                                                }
                                            }

                                            // don't forget the remaining literals which are not la
                                            newLaConstraints.addAll(res.remainingLiterals);

                                            Formula newConjunction = And.create(newLaConstraints);

                                            newAllConjunctions.add(newConjunction);
                                        }
                                    }
                                    Formula newFormula = Or.create(newAllConjunctions);

                                    LALemmaInsertionProof proof = new LALemmaInsertionProof(newFormula, constraintFormula, originallemma, specLemma);

                                    proofs.add(proof);
                                }
                            }
                            catch (UnificationException e) {
                            }
                        }
                    }

                }
            }

        }

        if(proofs.isEmpty()){
            return ResultFactory.notApplicable();
        }

        // compares size of the new formulas
        Comparator<LALemmaInsertionProof> compNewFormulas =
            new Comparator<LALemmaInsertionProof>(){

            @Override
            public int compare(LALemmaInsertionProof o1, LALemmaInsertionProof o2) {
                int o2size = o2.getNewFormulaSize();
                int o1size = o1.getNewFormulaSize();

                return o1size - o2size;
            }
        };
        Collections.sort(proofs, compNewFormulas);

        LALemmaInsertionProof selectedProof = proofs.get(0);

        TheoremProverObligation newObligation = new TheoremProverObligation(
                selectedProof.getNewFormula(),
                obligationInput);

        return ResultFactory.proved(newObligation, YNMImplication.COMPLETE, selectedProof);
    }

}

/**
 * The result of an abstraction is stored here
 */
class LAAbstractionResult{
    List<LinearConstraint> laConstraints;

    Formula premise;

    List<Formula> remainingLiterals;

    Map<AlgebraTerm, AlgebraVariable> abstraction;

    AlgebraSubstitution reverseAbstraction;

    Formula original;


    public LAAbstractionResult(Formula original,
            List<LinearConstraint> laConstraints,
            List<Formula> remainingLiterals,
            Map<AlgebraTerm, AlgebraVariable> abstraction) {
        this(original, laConstraints, remainingLiterals,
                abstraction, FormulaTruthValue.TRUE);
    }

    public LAAbstractionResult(Formula original,
            List<LinearConstraint> laConstraints,
            List<Formula> remainingLiterals,
            Map<AlgebraTerm, AlgebraVariable> abstraction,
            Formula premise) {
        this.original = original;
        this.laConstraints = laConstraints;
        this.remainingLiterals = remainingLiterals;
        this.abstraction = abstraction;
        this.premise = premise;

        // construct the substitution to undo the abstraction
        this.reverseAbstraction = AlgebraSubstitution.create();
        for (Entry<AlgebraTerm, AlgebraVariable> entry : this.abstraction.entrySet()) {
            this.reverseAbstraction.put(entry.getValue().getVariableSymbol(), entry.getKey());
        }

    }

    public LAAbstractionResult deepcopy(){
        List<LinearConstraint> newConstraints = new ArrayList<LinearConstraint>(this.laConstraints.size());
        for (LinearConstraint constraint : this.laConstraints) {
            newConstraints.add(constraint.deepcopy());
        }

        List<Formula> newRemainingLiterals = new ArrayList<Formula>(this.remainingLiterals.size());
        for (Formula lit : this.remainingLiterals) {
            newRemainingLiterals.add(lit.deepcopy());
        }


        Map<AlgebraTerm, AlgebraVariable> newAbstraction = new HashMap<AlgebraTerm, AlgebraVariable>(this.abstraction.size());
        Set<Entry<AlgebraTerm, AlgebraVariable>> absEntrySet = this.abstraction.entrySet();
        for (Entry<AlgebraTerm, AlgebraVariable> entry : absEntrySet) {
            newAbstraction.put(entry.getKey().deepcopy(), (AlgebraVariable)entry.getValue().deepcopy());
        }

        return new LAAbstractionResult(this.original.deepcopy(), newConstraints,
                newRemainingLiterals, newAbstraction, this.premise.deepcopy());
    }
}

/**
 * Traverses a conjunction and abstracts from uninterpreted function applications for Nat
 * by replacing them with variables.
 * At the same time LA constraints of type <= are consructed.
 * Equalities are split up into two <=
 */
class LALemmaAbstractionVisitor implements FineFormulaVisitor<Object>,
        CoarseGrainedTermVisitor<AlgebraTerm> {

    // constraints of type <=
    private List<LinearConstraint> constraints;

    private Map<AlgebraTerm, AlgebraVariable> abstraction;

    private List<Formula> literals;

    private LAProgramProperties laProgram;

    private boolean not;

    private FreshVarGenerator fvg;

    private AlgebraVariable abstractionVariable;

    private int doAbstraction;


    private LALemmaAbstractionVisitor(Set<AlgebraVariable> usedVariables, Map<AlgebraTerm, AlgebraVariable> abstraction, Program program) {

        // init object's variables
        if(abstraction==null){
            this.abstraction = new HashMap<AlgebraTerm, AlgebraVariable>();
        }
        else{
            this.abstraction = abstraction;
        }
        this.literals = new ArrayList<Formula>();
        this.laProgram = program.laProgramProperties;
        this.not = false;
        this.fvg = new FreshVarGenerator(usedVariables);
        VariableSymbol varsymb = VariableSymbol.create("A", this.laProgram.sortNat);
        this.abstractionVariable = AlgebraVariable.create(varsymb);
        this.doAbstraction = 0;
        this.constraints = new ArrayList<LinearConstraint>();
    }

    public static LAAbstractionResult apply(Formula formula, Set<AlgebraVariable> usedVariables, Program program) {
        return LALemmaAbstractionVisitor.apply(formula, usedVariables, null, program);
    }

    public static LAAbstractionResult apply(Formula formula, Set<AlgebraVariable> usedVariables, Map<AlgebraTerm, AlgebraVariable> abstraction, Program program) {

        LALemmaAbstractionVisitor laLemmaApplicationVisitor = new LALemmaAbstractionVisitor(
                usedVariables, abstraction, program);

        formula.apply(laLemmaApplicationVisitor);

        List<LinearConstraint> constraints = new ArrayList<LinearConstraint>(laLemmaApplicationVisitor.constraints.size());
        for (LinearConstraint constraint : laLemmaApplicationVisitor.constraints) {
            constraints.add(LinearIntegerConstraintSimplifier.toIntegerNormalForm(constraint));
        }

        ArrayList<Formula> resLiterals = new ArrayList<Formula>(constraints.size()
                + laLemmaApplicationVisitor.literals.size());
        resLiterals.addAll(laLemmaApplicationVisitor.literals);

        LAAbstractionResult res = new LAAbstractionResult(formula,
                laLemmaApplicationVisitor.constraints,
                laLemmaApplicationVisitor.literals,
                laLemmaApplicationVisitor.abstraction);

        return res;
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

            ConstraintType ct = constraint.getConstraintType();
            if(ct.equals(ConstraintType.EQUALITY)){
                // split into two <=
                LinearConstraint negConstraint = constraint.negate();

                constraint = constraint.changeConstraintType(ConstraintType.LESSEQ);
                negConstraint = negConstraint.changeConstraintType(ConstraintType.LESSEQ);

                this.constraints.add(constraint);
                this.constraints.add(negConstraint);
            }
            else if(ct.equals(ConstraintType.INEQUALITY)){
                throw new RuntimeException("there is still an inequality");
            }
            else{
                // change to type <=
                constraint = LinearIntegerConstraintSimplifier.toIntegerSyntactically(constraint);
                this.constraints.add(constraint);
            }
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
        this.constraints.add(constraint);

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
        return v.deepcopy();
    }
}


/**
 * Converts each lemma into a set of formulas of the form
 * A -> s=t or just s=t
 * And formulas and equivalencdes are split up into two formulas
 */
class LemmaConverter implements FineFormulaVisitor<List<Formula>>{

    public static List<Formula>  apply(Formula formula){
        LemmaConverter lc = new LemmaConverter();
        List<Formula> newFormulas = formula.apply(lc);
        return newFormulas;
    }

    private boolean impl = false;
    private boolean not = false;

    @Override
    public List<Formula> caseAnd(And andFormula) {
        List<Formula> newFormulas = new ArrayList<Formula>(2);
        if(this.not == true){
            // discard beacause formula to complex
            return newFormulas;
        }
        else{
            newFormulas.addAll(andFormula.getLeft().apply(this));
            newFormulas.addAll(andFormula.getRight().apply(this));
            return newFormulas;
        }
    }

    @Override
    public List<Formula> caseEquation(Equation phi) {
        List<Formula> newFormulas = new ArrayList<Formula>(1);
        if(this.not == true){

            newFormulas.add(Not.create(phi.deepcopy()));
        }
        else{
            newFormulas.add(phi.deepcopy());
        }
        return newFormulas;
    }

    @Override
    public List<Formula> caseEquivalence(Equivalence equivFormula) {
        List<Formula> newFormulas = new ArrayList<Formula>(2);

        if(this.not == true){
            // discard beacause formula to complex
            return newFormulas;
        }
        else{
            Formula left = equivFormula.getLeft();
            Formula right = equivFormula.getRight();

            Implication impl1 = Implication.create(left, right);
            Implication impl2 = Implication.create(right, left);

            newFormulas.addAll(impl1.apply(this));
            newFormulas.addAll(impl2.apply(this));

            return newFormulas;
        }
    }

    @Override
    public List<Formula> caseImplication(Implication implFormula) {
        List<Formula> newFormulas = new ArrayList<Formula>(1);
        if(this.not == true){
            // discard beacause formula to complex
            return newFormulas;
        }
        else{
            if(this.impl==true){
                // discard beacause formula to complex
                return newFormulas;
            }
            this.impl=true;
            Formula left = implFormula.getLeft();
            Formula right = implFormula.getRight();
            for (Formula newRight : right.apply(this)){
                newFormulas.add(Implication.create(left.deepcopy(), newRight));
            }

            this.impl=false;
            return newFormulas;
        }
    }

    @Override
    public List<Formula> caseNot(Not notFormula) {
        this.not = !this.not;
        List<Formula> newFormulas = new ArrayList<Formula>(1);
        newFormulas.addAll(notFormula.apply(this));
        this.not  = !this.not;
        return newFormulas;
    }

    @Override
    public List<Formula> caseOr(Or orFormula) {
        List<Formula> newFormulas = new ArrayList<Formula>(2);
        if(this.not == false){
            // discard beacause formula to complex
            return newFormulas;
        }
        else{
            newFormulas.addAll(orFormula.getLeft().apply(this));
            newFormulas.addAll(orFormula.getRight().apply(this));
            return newFormulas;
        }
    }

    @Override
    public List<Formula> caseTruthValue(FormulaTruthValue truthvalFormula) {
        List<Formula> newFormulas = new ArrayList<Formula>(1);
        newFormulas.add(truthvalFormula.deepcopy());
        return newFormulas;
    }
}
