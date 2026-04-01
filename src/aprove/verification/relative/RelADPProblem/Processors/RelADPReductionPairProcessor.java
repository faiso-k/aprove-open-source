package aprove.verification.relative.RelADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.relative.RelADPProblem.*;

/**
 * Reduction Pair Processor as described in [IJCAR24]
 * 
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public class RelADPReductionPairProcessor extends RelADPProblemProcessor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean allstrict;
    private final SolverFactory order;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public RelADPReductionPairProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.order = arguments.order;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isRelADPPApplicable(RelADPProblem reladpp) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processRelADPProblem(RelADPProblem oriqreladpp, Abortion aborter) throws AbortionException {

        final POLO order = this.findOrdering(oriqreladpp, this.allstrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful("Could not find a suitable poly interpretation");
        }

        /* find strict tuples */
        Set<Rule> oldD1 = oriqreladpp.getPAbs();
        Set<Rule> oldD2 = oriqreladpp.getPRel();
        Set<Rule> keptD1 = new HashSet<>();
        Set<Rule> keptD2 = new HashSet<>();
        Set<Rule> removedD1 = new HashSet<>();
        Set<Rule> removedD2 = new HashSet<>();

        for (Rule depTuple : oldD1) {
            if (!checkStrictDecrease(depTuple, order, aborter, oriqreladpp)) {
                keptD1.add(depTuple);
            } else if (depTuple.getRight().countAnnos(oriqreladpp.getDeannotator().keySet()) > 0){
                removedD1.add(depTuple);
            }
        }
        for (Rule depTuple : oldD2) {
            if (depTuple.getRight().countAnnos(oriqreladpp.getDeannotator().keySet()) > 0
                            && !checkStrictDecrease(depTuple, order, aborter, oriqreladpp)) {
                keptD2.add(depTuple);
            } else if (depTuple.getRight().countAnnos(oriqreladpp.getDeannotator().keySet()) > 0){
                removedD2.add(depTuple);
            }
        }

        Set<Rule> newPAbs = new HashSet<>();
        Set<Rule> newPRel = new HashSet<>();
        
        for(Rule rule : oriqreladpp.getPAbs()) {
            if(keptD1.contains(rule)) {
                newPAbs.add(rule);
            } else {
                removedD1.add(rule);
                if(rule.getRight() instanceof TRSFunctionApplication) {
                    TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
                    Rule disAnnoRule = Rule.create(rule.getLeft(), rhs.renameAtAllMap(rule.getRight().getPositions(), oriqreladpp.getDeannotator()));
                    newPRel.add(disAnnoRule);
                } else {
                    newPRel.add(rule);
                }
            }
        }
        
        for(Rule rule : oriqreladpp.getPRel()) {
            if(keptD2.contains(rule)) {
                newPRel.add(rule);
            } else {
                removedD2.add(rule);
                if(rule.getRight() instanceof TRSFunctionApplication) {
                    TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
                    Rule disAnnoRule = Rule.create(rule.getLeft(), rhs.renameAtAllMap(rule.getRight().getPositions(), oriqreladpp.getDeannotator()));
                    newPRel.add(disAnnoRule);
                } else {
                    newPRel.add(rule);
                }
            }
        }
        
        RelADPProblem newpqdp = RelADPProblem.create(newPAbs, newPRel, oriqreladpp.getQ(), oriqreladpp.getBiAnnoMap());

        RelADPReductionPairProof RPPproof = new RelADPReductionPairProof(order, oriqreladpp, newpqdp, removedD1,
                keptD1, removedD2, keptD2);

        return ResultFactory.proved(newpqdp, YNMImplication.EQUIVALENT, RPPproof);
    }

    /**
     * The SMT-Solving part of the processor.
     * This includes the creation of an interpretation, the formula about diophantine constraints
     * and the search for a satisfying interpretation via some solver.
     * 
     * @param pqdpProblem - the original PQDPProblem problem
     * @param allstrict - boolean whether we want to strict all of the rules strictly
     * @param aborter - Aborter to check the timer
     * @return the satisfying polynomial interpretation
     * @throws AbortionException
     */
    private POLO findOrdering(final RelADPProblem pqdpProblem, final boolean allstrict, final Abortion aborter)
            throws AbortionException {

        POLOSolver solver = this.order.getPOLOSolver(pqdpProblem.getSignature(), aborter);
        solver.setAllowWeakMonotonicity(true);
        
        Interpretation interpretation = solver.getInterpretation();
        
        for(FunctionSymbol f : pqdpProblem.getAnnotatedSignature()) {
            if(!pqdpProblem.getSignature().contains(f)) {
                interpretation.extend(f, 0, aborter);
            }
        }

        final Formula<Diophantine> fml = this.createFormula(pqdpProblem, interpretation, aborter);

        return solver.solveDioFormula(fml, aborter);
    }

    /**
     * Create the formula that we need to satisfy
     * (All expected values are non increasing, at least one element in the support of the rhs is strictly decreasing)
     * 
     * @param pqdpProblem - the original PQDPProblem problem
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return The complete formula for the probabilistic RPP
     */
    private Formula<Diophantine> createFormula(
        final RelADPProblem pqdpProblem,
        Interpretation interpretation,
        final Abortion aborter
    ) {
        final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB); //TODO: Check these parameters

        Set<Rule> D1 = pqdpProblem.getPAbs();
        Set<Rule> D2 = pqdpProblem.getPRel();
        Set<Rule> R = pqdpProblem.getR();

        // Create the Formula of Constraints that we want to solve:
        // 1) for all l->r in R: l >= r
        List<Formula<Diophantine>> nonHashedConstraintList = new ArrayList<>(R.size());
        for (Rule rule: R) {
            nonHashedConstraintList.add(createRuleFormulaExpectation(ff, rule, interpretation, aborter));
        }

        // 2) for all l->r in PAbs u PRel: depterm(l) >= depterm(t)
        List<Formula<Diophantine>> nonStrictConstraintList = new ArrayList<>(D1.size() + D2.size());
        for (Rule rule: D1) {
            nonStrictConstraintList.add(createADPFormulaNonStrict(ff, rule, interpretation, aborter, pqdpProblem));
        }
        for (Rule rule: D2) {
            nonStrictConstraintList.add(createADPFormulaNonStrict(ff, rule, interpretation, aborter, pqdpProblem));
        }

        // 3) for all l->r in PAbs and all l->r in PRel with annotations: depterm(l) > tepterm(t) (if possible)
        List<Formula<Diophantine>> strictConstraintList = new ArrayList<>(D1.size() + D2.size());
        for (Rule rule : D1) {
            strictConstraintList.add(createADPFormulaStrict(ff, rule, interpretation, aborter, pqdpProblem));
        }for (Rule rule : D2) {
            if(rule.getRight().countAnnos(pqdpProblem.getDeannotator().keySet()) > 0) {
                strictConstraintList.add(createADPFormulaStrict(ff, rule, interpretation, aborter, pqdpProblem));
            }
        }

        Formula<Diophantine> nonHashedConstraintFormula = ff.buildAnd(nonHashedConstraintList);
        Formula<Diophantine> nonStrictConstraintFormula;
        Formula<Diophantine> strictConstraintFormula;

        if (allstrict) {  // I guess in some cases we want it to be true for everything? idk
            strictConstraintFormula = ff.buildAnd(strictConstraintList);
            nonStrictConstraintFormula = ff.buildAnd(nonStrictConstraintList);
        } else {
            strictConstraintFormula = ff.buildOr(strictConstraintList);
            nonStrictConstraintFormula = ff.buildAnd(nonStrictConstraintList);
        }

        List<Formula<Diophantine>> finalConstraintsList = new ArrayList<>();
        finalConstraintsList.add(nonHashedConstraintFormula);
        finalConstraintsList.add(strictConstraintFormula);
        finalConstraintsList.add(nonStrictConstraintFormula);
        Formula<Diophantine> finalFormula = ff.buildAnd(finalConstraintsList);

        return finalFormula;
    }

    /**
     * @param ff - FormulaFactory for formulas about Diophantine constraints
     * @param rule - the probabilistic rewrite rule for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "expectation non-increasing"
     */
    private Formula<Diophantine> createRuleFormulaExpectation(
        FormulaFactory<Diophantine> ff, Rule rule,
        Interpretation interpretation, Abortion aborter
    ) {
        VarPolynomial rhsExpectedPoly = VarPolynomial.ZERO;

        TRSTerm term = rule.getRight();

        rhsExpectedPoly = rhsExpectedPoly.plus(interpretation.interpretTerm(term, aborter));

        VarPolynomial lhsPoly = (interpretation.interpretTerm(rule.getLeft(), aborter));
        VarPolynomial constraint = lhsPoly.minus(rhsExpectedPoly);
        Set<SimplePolyConstraint> simplePolyConstraintSet = new VarPolyConstraint(constraint, ConstraintType.GE)
                .createCoefficientConstraints();
        List<Formula<Diophantine>> ruleFormulaList = new ArrayList<>();
        for (SimplePolyConstraint spc : simplePolyConstraintSet) {
            Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            ruleFormulaList.add(helpFormula);
        }
        return ff.buildAnd(ruleFormulaList);
    }

    /**
     * @param ff - FormulaFactory for formulas about Diophantine constraints
     * @param rule - the probabilistic dependency tuple for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "expectation non-increasing"
     */
    private Formula<Diophantine> createADPFormulaNonStrict(
        FormulaFactory<Diophantine> ff,
        Rule rule,
        Interpretation interpretation,
        Abortion aborter,
        RelADPProblem problem
    ) {
        TRSTerm lhs_anno = rule.getLeft().renameAtMap(Position.EPSILON, problem.getAnnotator());
        TRSTerm rhs = rule.getRight();

        VarPolynomial annoTermPoly = VarPolynomial.ZERO;

        for (TRSFunctionApplication subterm : rhs.subAnnoTerms(problem.getDeannotator())) {
            annoTermPoly = annoTermPoly.plus(interpretation.interpretTerm(subterm, aborter));
        }

        VarPolynomial lhsPoly = (interpretation.interpretTerm(lhs_anno, aborter));
        VarPolynomial constraint = lhsPoly.minus(annoTermPoly);
        Set<SimplePolyConstraint> simplePolyConstraintSet = new VarPolyConstraint(constraint, ConstraintType.GE)
                .createCoefficientConstraints();
        List<Formula<Diophantine>> ruleFormulaList = new ArrayList<>();
        for (SimplePolyConstraint spc : simplePolyConstraintSet) {
            Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            ruleFormulaList.add(helpFormula);
        }
        return ff.buildAnd(ruleFormulaList);
    }

    /**
     * @param ff - FormulaFactory for formulas about Diophantine constraints
     * @param rule - the probabilistic rewrite rule for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "one element in the support of rhs is strictly decreasing"
     */
    private Formula<Diophantine> createADPFormulaStrict(
        FormulaFactory<Diophantine> ff,
        Rule rule,
        Interpretation interpretation,
        Abortion aborter,
        RelADPProblem problem
    ) {
        TRSTerm lhs_anno = rule.getLeft().renameAtMap(Position.EPSILON, problem.getAnnotator());
        TRSTerm rhs = rule.getRight();

        VarPolynomial annoTermPoly = VarPolynomial.ZERO;

        for (TRSFunctionApplication subterm : rhs.subAnnoTerms(problem.getDeannotator())) {
            annoTermPoly = annoTermPoly.plus(interpretation.interpretTerm(subterm, aborter));
        }

        VarPolynomial lhsPoly = (interpretation.interpretTerm(lhs_anno, aborter));
        VarPolynomial constraint = lhsPoly.minus(annoTermPoly);
        Set<SimplePolyConstraint> simplePolyConstraintSet = new VarPolyConstraint(constraint, ConstraintType.GT)
                .createCoefficientConstraints();
        List<Formula<Diophantine>> ruleFormulaList = new ArrayList<>();
        for (SimplePolyConstraint spc : simplePolyConstraintSet) {
            Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            ruleFormulaList.add(helpFormula);
        }
        return ff.buildAnd(ruleFormulaList);
    }

    /**
     * @param rule - the probabilistic rewrite rule for this formula
     * @param order - the polynomial interpretation that solved the RPP formula
     * @param aborter - Aborter to check the timer
     * @return true, if the rule together with the polynomial interpretation stored in order satisfies the "strictly decreasing" formula
     */
    private boolean checkStrictDecrease(Rule rule, final POLO order, Abortion aborter, RelADPProblem problem) {
        VarPolynomial lhs_deanno = (order.getInterpretation().interpretTerm(rule.getLeft(), aborter));
        VarPolynomial lhs_anno = (order.getInterpretation().interpretTerm(rule.getLeft().renameAtMap(Position.EPSILON, problem.getAnnotator()), aborter));

        VarPolynomial rhs_deanno;
        if (rule.getRight().isVariable()) {
            rhs_deanno = (order.getInterpretation().interpretTerm(rule.getRight(), aborter));
        } else {
            TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
            rhs_deanno = (order.getInterpretation().interpretTerm(rhs.renameAtAllMap(rhs.getPositions(), problem.getDeannotator()), aborter));
        }

//        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = rule.getRightPair();
        boolean firstProperty, secondProperty = false;

        //Make sure that that the Tuple part is strictly smaller
        VarPolynomial setPoly = VarPolynomial.ZERO;
//        for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
        for (TRSFunctionApplication subDepTerm : rule.getRight().subAnnoTerms(problem.getDeannotator())) {
            setPoly = setPoly.plus(order.getInterpretation().interpretTerm(subDepTerm, aborter));
        }
        VarPolynomial tupleConstraintPoly = lhs_anno.minus(setPoly);

        VarPolyConstraint tupleConstraint = new VarPolyConstraint(tupleConstraintPoly, ConstraintType.GT);
        firstProperty = tupleConstraint.isValid();

        //Make sure that that the TRS part is smaller or equal
//        VarPolynomial termPoly = order.getInterpretation().interpretTerm(coupledSetTermElement.y, aborter);
        VarPolynomial termConstraintPoly = lhs_deanno.minus(rhs_deanno);

        VarPolyConstraint termConstraint = new VarPolyConstraint(termConstraintPoly, ConstraintType.GE);
        secondProperty = termConstraint.isValid();

        if (firstProperty && secondProperty)
            return true;
        return false;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class RelADPReductionPairProof extends RelADPProof {

        private final ExportableOrder<TRSTerm> order;
        private final RelADPProblem origreladpp;
        private final RelADPProblem newreladpp;
        private final Set<Rule> removedD1;
        private final Set<Rule> keptD1;
        private final Set<Rule> removedD2;
        private final Set<Rule> keptD2;

        RelADPReductionPairProof(
            final ExportableOrder<TRSTerm> order,
            final RelADPProblem origreladpp,
            final RelADPProblem newreladpp,
            final Set<Rule> removedD1,
            final Set<Rule> keptD1,
            final Set<Rule> removedD2,
            final Set<Rule> keptD2
        ) {
            this.order = order;
            this.origreladpp = origreladpp;
            this.newreladpp = newreladpp;
            this.removedD1 = removedD1;
            this.keptD1 = keptD1;
            this.removedD2 = removedD2;
            this.keptD2 = keptD2;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append(o.paragraph());
            result.append("We use the reduction pair processor " + o.cite(Citation.IJCAR24) + ".");
            result.append(o.linebreak());
            result.append("The following rules can be oriented strictly (l^# > ann(r)) ");
            result.append(o.linebreak());
            result.append("and therefore we can remove all of its annotations in the right-hand side:");
            result.append(o.cond_linebreak());
            if (this.removedD1.size() > 0) {
                result.append("Absolute ADPs:");
                result.append(o.linebreak());
                result.append(o.set(this.removedD1, Export_Util.RULES));   
                result.append(o.linebreak());
            }
            if (this.removedD2.size() > 0) {
                result.append("Relative ADPs:");
                result.append(o.linebreak());
                result.append(o.set(this.removedD2, Export_Util.RULES));
                result.append(o.linebreak());
            }
            result.append(o.cond_linebreak());
            if (this.keptD1.size() + this.keptD2.size() > 0) {
                result.append("The remaining rules can at least be oriented weakly:");
                result.append(o.cond_linebreak());
                if (this.keptD1.size() > 0) {
                    result.append("Absolute ADPs:");
                    result.append(o.linebreak());
                    result.append(o.set(this.keptD1, Export_Util.RULES));
                    result.append(o.linebreak());
                }
                if (this.keptD1.size() > 0) {
                    result.append("Relative ADPs:");
                    result.append(o.linebreak());
                    result.append(o.set(this.keptD2, Export_Util.RULES)); 
                    result.append(o.linebreak());                   
                }
            } else {
                result.append("No rules with annotations remain.");
            }
            result.append(o.cond_linebreak());
            result.append("Ordered with ");
            result.append(this.order.export(o));

            return result.toString();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {

        public boolean allstrict = false;
        public SolverFactory order;
    }

}
