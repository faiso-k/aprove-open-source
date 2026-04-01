package aprove.verification.relative.RelADPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.relative.RelADPProblem.*;
import immutables.*;

/**
 * Rule Removal Processor as described in [IJCAR24]
 * 
 * @author Grigory Vartanyan, Jan-Christoph Kassing
 * @version $Id$
 */
public class RelADPRuleRemovalProcessor extends RelADPProblemProcessor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean allstrict;
    private final SolverFactory order;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public RelADPRuleRemovalProcessor(final Arguments arguments) {
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
        Set<Rule> oldRules = new HashSet<>(oriqreladpp.getR());

        for (Rule depTuple : oldD1) {
            if (!checkStrictDecrease(depTuple, order, aborter, oriqreladpp)) {
                keptD1.add(depTuple);
            } else {
                removedD1.add(depTuple);
                if (depTuple.getRight().isVariable()) {
                    oldRules.remove(depTuple);
                } else {
                    var rhs = (TRSFunctionApplication) depTuple.getRight();
                    var rhs_deanno = rhs.renameAtAllMap(rhs.getPositions(), oriqreladpp.getDeannotator());
                    var rule = Rule.create(depTuple.getLeft(), rhs_deanno);
                    oldRules.remove(rule);
                }
            }
        }
        for (Rule depTuple : oldD2) {
            if (!checkStrictDecrease(depTuple, order, aborter, oriqreladpp)) {
                keptD2.add(depTuple);
            } else {
                removedD2.add(depTuple);
                if (depTuple.getRight().isVariable()) {
                    oldRules.remove(depTuple);
                } else {
                    var rhs = (TRSFunctionApplication) depTuple.getRight();
                    var rhs_deanno = rhs.renameAtAllMap(rhs.getPositions(), oriqreladpp.getDeannotator());
                    var rule = Rule.create(depTuple.getLeft(), rhs_deanno);
                    oldRules.remove(rule);
                }
            }
        }

        ImmutableSet<Rule> newRules = ImmutableCreator.create(oldRules);

        QTRSProblem newpqtrs = QTRSProblem.create(newRules, oriqreladpp.getQ().getQ());
        RelADPProblem newpqdp = RelADPProblem.create(keptD1, keptD2, newpqtrs, oriqreladpp.getBiAnnoMap());

        RelADPRuleRemovalProof RRPproof = new RelADPRuleRemovalProof(order, oriqreladpp, newpqdp, removedD1,
                keptD1, removedD2, keptD2);

        return ResultFactory.proved(newpqdp, YNMImplication.EQUIVALENT, RRPproof);
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

        final Formula<Diophantine> fml = this.createFormula(pqdpProblem, solver.getInterpretation(), aborter);

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
        List<Formula<Diophantine>> nonStrictConstraintList = new ArrayList<>(R.size());  // strict upper bound
        for (Rule rule: R) {
            nonStrictConstraintList.add(createRuleNonStrictFormulaExpectation(ff, rule, interpretation, aborter));
        }

        // 3) for all l->r in PAbs u PRel: depterm(l) >= tepterm(t) (if posible)
        List<Formula<Diophantine>> strictConstraintList = new ArrayList<>(R.size());
        for (Rule rule: R) {
            strictConstraintList.add(createRuleStrictFormulaExpectation(ff, rule, interpretation, aborter));
        }

        Formula<Diophantine> nonStrictConstraintFormula;
        Formula<Diophantine> strictConstraintFormula;

        if (allstrict) {  // I guess in some cases we want it to be true for everything? idk
            strictConstraintFormula = ff.buildAnd(strictConstraintList);
            nonStrictConstraintFormula = ff.buildAnd(nonStrictConstraintList);
        } else {
            nonStrictConstraintFormula = ff.buildAnd(nonStrictConstraintList);
            strictConstraintFormula = ff.buildOr(strictConstraintList);
        }

        List<Formula<Diophantine>> monotonicityConstraintsList = new ArrayList<>();
        Set<SimplePolyConstraint> simplePolyConstraints = new HashSet<>();
        
        simplePolyConstraints.addAll(interpretation.getStrongMonotonicityConstraints(null));
        for(SimplePolyConstraint spc : simplePolyConstraints) {
            Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            monotonicityConstraintsList.add(helpFormula);
        }

        List<Formula<Diophantine>> finalConstraintsList = new ArrayList<>();
        finalConstraintsList.add(strictConstraintFormula);
        finalConstraintsList.add(nonStrictConstraintFormula);
        finalConstraintsList.addAll(monotonicityConstraintsList);
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
    private Formula<Diophantine> createRuleNonStrictFormulaExpectation(
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
     * @param rule - the probabilistic rewrite rule for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "expectation non-increasing"
     */
    private Formula<Diophantine> createRuleStrictFormulaExpectation(
        FormulaFactory<Diophantine> ff, Rule rule,
        Interpretation interpretation, Abortion aborter
    ) {
        VarPolynomial rhsExpectedPoly = VarPolynomial.ZERO;

        TRSTerm term = rule.getRight();

        rhsExpectedPoly = rhsExpectedPoly.plus(interpretation.interpretTerm(term, aborter));

        VarPolynomial lhsPoly = (interpretation.interpretTerm(rule.getLeft(), aborter));
        VarPolynomial constraint = lhsPoly.minus(rhsExpectedPoly);
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

        VarPolynomial rhs_deanno;
        if (rule.getRight().isVariable()) {
            rhs_deanno = (order.getInterpretation().interpretTerm(rule.getRight(), aborter));
        } else {
            TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();
            rhs_deanno = (order.getInterpretation().interpretTerm(rhs.renameAtAllMap(rhs.getPositions(), problem.getDeannotator()), aborter));
        }

        VarPolynomial termConstraintPoly = lhs_deanno.minus(rhs_deanno);

        VarPolyConstraint termConstraint = new VarPolyConstraint(termConstraintPoly, ConstraintType.GT);
        return termConstraint.isValid();
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class RelADPRuleRemovalProof extends RelADPProof {

        private final ExportableOrder<TRSTerm> order;
        private final RelADPProblem origreladpp;
        private final RelADPProblem newreladpp;
        private final Set<Rule> removedD1;
        private final Set<Rule> keptD1;
        private final Set<Rule> removedD2;
        private final Set<Rule> keptD2;

        RelADPRuleRemovalProof(
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
            result.append("We use the rule removal processor " + o.cite(Citation.IJCAR24) + ".");
            result.append(o.linebreak());
            result.append("The following rules can be ordered strictly and therefore removed:");
            result.append(o.cond_linebreak());
            if (this.removedD1.size() > 0) {
                result.append(o.set(this.removedD1, Export_Util.RULES));   
            }
            if (this.removedD2.size() > 0) {
                result.append(o.set(this.removedD2, Export_Util.RULES));
            }
            result.append(o.cond_linebreak());
            if (this.keptD1.size() + this.keptD2.size() > 0) {
                result.append("c:");
                result.append(o.cond_linebreak());
                if (this.keptD1.size() > 0) {
                    result.append(o.set(this.keptD1, Export_Util.RULES));
                }
                if (this.keptD1.size() > 0) {
                    result.append(o.set(this.keptD2, Export_Util.RULES));                    
                }
            } else {
                result.append("No rules remain.");
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
