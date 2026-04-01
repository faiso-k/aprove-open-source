package aprove.verification.relative.RDTProblem.Processors;

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
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.relative.RDTProblem.*;
import immutables.*;

/**
 * Reduction Pair Processor as described in Vartanyan's bachelor's thesis
 * 
 * @author Grigory Vartanyan
 * @version $Id$
 */
public class RDTReductionPairProcessor extends RDTProblemProcessor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean allstrict;
    private final SolverFactory order;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public RDTReductionPairProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.order = arguments.order;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isRDTPApplicable(RDTProblem qdp) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processRDTProblem(RDTProblem oriqpqdp, Abortion aborter) throws AbortionException {

        final POLO order = this.findOrdering(oriqpqdp, this.allstrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful("Could not find a suitable poly interpretation");
        }

        /* find strict tuples */
        Set<CoupledPosDepTuple> oldD1 = oriqpqdp.getD1();
        Set<CoupledPosDepTuple> oldD2 = oriqpqdp.getD2();
        Set<CoupledPosDepTuple> keptD1 = new HashSet<>();
        Set<CoupledPosDepTuple> keptD2 = new HashSet<>();
        Set<CoupledPosDepTuple> removedD1 = new HashSet<>();
        Set<CoupledPosDepTuple> removedD2 = new HashSet<>();
        ImmutableSet<Rule> oldRules = ImmutableCreator.create(oriqpqdp.getR());

        for (CoupledPosDepTuple depTuple : oldD1) {
            if (!checkStrictDecrease(depTuple, order, aborter)) {
                keptD1.add(depTuple);
            } else {
                removedD1.add(depTuple);
            }
        }
        for (CoupledPosDepTuple depTuple : oldD2) {
            if (!checkStrictDecrease(depTuple, order, aborter)) {
                keptD2.add(depTuple);
            } else {
                removedD2.add(depTuple);
            }
        }

        QTRSProblem newpqtrs = QTRSProblem.create(oldRules, oriqpqdp.getQ().getQ());  // TODO: isn't this empty?
        RDTProblem newpqdp = RDTProblem.create(keptD1, keptD2, newpqtrs);

        RDTReductionPairProof RPPproof = new RDTReductionPairProof(order, oriqpqdp, newpqdp, removedD1,
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
    private POLO findOrdering(final RDTProblem pqdpProblem, final boolean allstrict, final Abortion aborter)
            throws AbortionException {

        POLOSolver solver = this.order.getMLPOLOSolver(pqdpProblem.getSignature(), aborter);
        solver.setAllowWeakMonotonicity(true);

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
    private Formula<Diophantine> createFormula(final RDTProblem pqdpProblem, Interpretation interpretation,
            final Abortion aborter) {

        final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB); //TODO: Check these parameters

        Set<CoupledPosDepTuple> D1 = pqdpProblem.getD1();
        Set<CoupledPosDepTuple> D2 = pqdpProblem.getD2();
        Set<Rule> R = pqdpProblem.getR();

        //Create the Formula of Constraints that we want to solve:
        // I have no idea what I'm doing, just copying Kassing's thing from the pdf
        
        // 1) for all l->r in R, for all l#,l->C,r in D1uD2: Pol(l) >= Pol(r)
        List<Formula<Diophantine>> nonHashedConstraintList = new ArrayList<>(R.size() + D1.size() + D2.size());
        for (Rule r: R) {
            nonHashedConstraintList.add(createRuleFormulaExpectation(ff, r, interpretation, aborter));
        }
        for (CoupledPosDepTuple depTuple : D1) {
            var r = Rule.create(depTuple.getLeft(), depTuple.getRightPair().getValue());
            nonHashedConstraintList.add(createRuleFormulaExpectation(ff, r, interpretation, aborter));
        }
        for (CoupledPosDepTuple depTuple : D2) {
            var r = Rule.create(depTuple.getLeft(), depTuple.getRightPair().getValue());
            nonHashedConstraintList.add(createRuleFormulaExpectation(ff, r, interpretation, aborter));
        }
        Formula<Diophantine> nonHashedConstraintFormula = ff.buildAnd(nonHashedConstraintList);


        // 2) for all l#,l->C,r in D1> u D2>: Pol(l#) > Pol(C)
        List<Formula<Diophantine>> strictConstraintList = new ArrayList<>(D1.size() + D2.size());
        for (CoupledPosDepTuple depTuple : D1) {
            strictConstraintList.add(createDepTupleFormulaStrict(ff, depTuple, interpretation, aborter));
        }
        for (CoupledPosDepTuple depTuple : D2) {
            strictConstraintList.add(createDepTupleFormulaStrict(ff, depTuple, interpretation, aborter));
        }
        

        // 3) for all l#,l->C,r in D1>> u D2>>: Pol(l#) >= Pol(C)
        List<Formula<Diophantine>> nonStrictConstraintList = new ArrayList<>(D1.size() + D2.size());
        for (CoupledPosDepTuple depTuple : D1) {
            nonStrictConstraintList.add(createDepTupleFormulaNonStrict(ff, depTuple, interpretation, aborter));
        }
        for (CoupledPosDepTuple depTuple : D2) {
            nonStrictConstraintList.add(createDepTupleFormulaNonStrict(ff, depTuple, interpretation, aborter));
        }


        Formula<Diophantine> strictConstraintFormula;
        Formula<Diophantine> nonStrictConstraintFormula;
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
    private Formula<Diophantine> createRuleFormulaExpectation(FormulaFactory<Diophantine> ff, Rule rule,
            Interpretation interpretation, Abortion aborter) {
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

    /** DONE
     * @param ff - FormulaFactory for formulas about Diophantine constraints
     * @param rule - the probabilistic dependency tuple for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "expectation non-increasing"
     */
    private Formula<Diophantine> createDepTupleFormulaNonStrict(
        FormulaFactory<Diophantine> ff,
        CoupledPosDepTuple rule,
        Interpretation interpretation,
        Abortion aborter
    ) {
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = rule.getRightPair();

        VarPolynomial setPoly = VarPolynomial.ZERO;

        for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
            setPoly = setPoly.plus(interpretation.interpretTerm(termPositionPair.x, aborter));
        }

        VarPolynomial lhsPoly = (interpretation.interpretTerm(rule.getTupleLeft(), aborter));
        VarPolynomial constraint = lhsPoly.minus(setPoly);
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
    private Formula<Diophantine> createDepTupleFormulaStrict(
        FormulaFactory<Diophantine> ff,
        CoupledPosDepTuple rule,
        Interpretation interpretation,
        Abortion aborter
    ) {
        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = rule.getRightPair();

        VarPolynomial setPoly = VarPolynomial.ZERO;

        for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
            setPoly = setPoly.plus(interpretation.interpretTerm(termPositionPair.x, aborter));
        }

        VarPolynomial lhsPoly = (interpretation.interpretTerm(rule.getTupleLeft(), aborter));
        VarPolynomial constraint = lhsPoly.minus(setPoly);
        Set<SimplePolyConstraint> simplePolyConstraintSet = new VarPolyConstraint(constraint, ConstraintType.GT)
                .createCoefficientConstraints();
        List<Formula<Diophantine>> ruleFormulaList = new ArrayList<>();
        for (SimplePolyConstraint spc : simplePolyConstraintSet) {
            Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            ruleFormulaList.add(helpFormula);
        }
        return ff.buildAnd(ruleFormulaList);
    }

    /** DONE
     * @param rule - the probabilistic rewrite rule for this formula
     * @param order - the polynomial interpretation that solved the RPP formula
     * @param aborter - Aborter to check the timer
     * @return true, if the rule together with the polynomial interpretation stored in order satisfies the "strictly decreasing" formula
     */
    private boolean checkStrictDecrease(CoupledPosDepTuple rule, final POLO order, Abortion aborter) {
        VarPolynomial lhsTuplePoly = (order.getInterpretation().interpretTerm(rule.getTupleLeft(), aborter));
        VarPolynomial lhsTermPoly = (order.getInterpretation().interpretTerm(rule.getLeft(), aborter));

        Pair<Set<Pair<TRSFunctionApplication, Position>>, ? extends TRSTerm> coupledSetTermElement = rule.getRightPair();
        boolean firstProperty, secondProperty = false;

        //Make sure that that the Tuple part is strictly smaller
        VarPolynomial setPoly = VarPolynomial.ZERO;
        for (Pair<TRSFunctionApplication, Position> termPositionPair : coupledSetTermElement.x) {
            setPoly = setPoly.plus(order.getInterpretation().interpretTerm(termPositionPair.x, aborter));
        }
        VarPolynomial tupleConstraintPoly = lhsTuplePoly.minus(setPoly);

        VarPolyConstraint tupleConstraint = new VarPolyConstraint(tupleConstraintPoly, ConstraintType.GT);
        firstProperty = tupleConstraint.isValid();

        //Make sure that that the TRS part is smaller or equal
        VarPolynomial termPoly = order.getInterpretation().interpretTerm(coupledSetTermElement.y, aborter);
        VarPolynomial termConstraintPoly = lhsTermPoly.minus(termPoly);

        VarPolyConstraint termConstraint = new VarPolyConstraint(termConstraintPoly, ConstraintType.GE);
        secondProperty = termConstraint.isValid();

        if (firstProperty && secondProperty)
            return true;
        return false;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class RDTReductionPairProof extends RDTProof {

        private final ExportableOrder<TRSTerm> order;
        private final RDTProblem origPQDP;
        private final RDTProblem newPQDP;
        private final Set<CoupledPosDepTuple> removedD1;
        private final Set<CoupledPosDepTuple> keptD1;
        private final Set<CoupledPosDepTuple> removedD2;
        private final Set<CoupledPosDepTuple> keptD2;

        RDTReductionPairProof(
            final ExportableOrder<TRSTerm> order,
            final RDTProblem origqdp,
            final RDTProblem resultingQDP,
            final Set<CoupledPosDepTuple> removedD1,
            final Set<CoupledPosDepTuple> keptD1,
            final Set<CoupledPosDepTuple> removedD2,
            final Set<CoupledPosDepTuple> keptD2
        ) {
            this.order = order;
            this.origPQDP = origqdp;
            this.newPQDP = resultingQDP;
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
            result.append("We use the reduction pair processor " + o.cite(Citation.VARTANYAN_BA) + ".");
            result.append(o.linebreak());
            result.append("The following tuples can be oriented strictly and therefore removed:");
            result.append(o.cond_linebreak());
            if (this.removedD1.size() > 0) {
                result.append(o.set(this.removedD1, Export_Util.RULES));   
            }
            if (this.removedD2.size() > 0) {
                result.append(o.set(this.removedD2, Export_Util.RULES));
            }
            result.append(o.cond_linebreak());
            if (this.keptD1.size() + this.keptD2.size() > 0) {
                result.append("The remaining tuples can at least be oriented weakly:");
                result.append(o.cond_linebreak());
                if (this.keptD1.size() > 0) {
                    result.append(o.set(this.keptD1, Export_Util.RULES));
                }
                if (this.keptD1.size() > 0) {
                    result.append(o.set(this.keptD2, Export_Util.RULES));                    
                }
            } else {
                result.append("No tuples remain.");
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
