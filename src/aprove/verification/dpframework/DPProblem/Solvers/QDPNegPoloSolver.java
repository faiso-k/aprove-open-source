package aprove.verification.dpframework.DPProblem.Solvers;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.solver.*;
import aprove.solver.NEGPOLOFactory.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.NegativePolynomials.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.QApplicativeUsableRules.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Algebra.Polynomials.SPCFormulae.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * QDP Polo processor. Tries to orient P and all usable rules of P non-strictly
 * and at least one rule of P strictly, then deletes the strictly oriented
 * rules from P.
 *
 * @author Rene Thiemann
 * @version $Id$
 */
public class QDPNegPoloSolver implements ImprovedQActiveSolver {

    private static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Solvers.QDPNegPoloSolver");

    private final BigInteger range;
    private final BigInteger posConstantRange;
    private final BigInteger negConstantRange;
    private final int restriction;
    private final Engine engine;
    private final DiophantineSATConverter dioSatConv;
    private final NegRangeCriterion negRangeCriterion;
    private final boolean partialDioEval;

    /**
     * This constructor is probably most useful if you intend to use
     * SATNegPOLOSolver.
     *
     * @param range
     * @param posConstantRange
     * @param negConstantRange
     * @param engine
     * @param dioSatConv
     */
    public QDPNegPoloSolver(BigInteger range, BigInteger posConstantRange,
            BigInteger negConstantRange, SatEngine engine,
            DiophantineSATConverter dioSatConv,
            NegRangeCriterion negRangeCriterion, boolean partialDioEval) {
        this.range = range;
        this.posConstantRange = posConstantRange;
        this.negConstantRange = negConstantRange;
        this.restriction = 0;
        this.engine = engine;
        this.dioSatConv = dioSatConv;
        this.negRangeCriterion = negRangeCriterion;
        this.partialDioEval = partialDioEval;
    }

    /**
     * This constructor is probably most useful if you intend to use
     * DynamicNegPOLOSolver.
     *
     * @param range
     * @param restriction
     * @param engine
     */
    public QDPNegPoloSolver(BigInteger range, int restriction, Engine engine) {
        this.range = range;
        this.posConstantRange = range.abs();
        this.negConstantRange = range.signum() > 0 ? BigInteger.ZERO : range;
        this.restriction = restriction;
        this.engine = engine;
        this.dioSatConv = null;
        this.negRangeCriterion = null;
        this.partialDioEval = false;
    }

    @Override
    public QActiveOrder solveQActive(Set<? extends GeneralizedRule> P, Map<? extends GeneralizedRule, QActiveCondition> R,
            boolean active, boolean allstrict,Abortion aborter) throws AbortionException {
        if (this.engine instanceof SatEngine) {
            SatEngine satEngine = (SatEngine) this.engine;
            return NegPoloInterpretation.solve(P, R, this.range.abs(),
                    this.posConstantRange, this.negConstantRange, allstrict,
                    this.dioSatConv, satEngine, this.negRangeCriterion,
                    this.partialDioEval, aborter);
        }
        else {
            // TODO port DynamicNegPOLOSolver to BigInteger?
            int rangeInt = this.range.intValue();
            if (BigInteger.valueOf(rangeInt).equals(this.range)) {
                NegPOLOSolver solver = new DynamicNegPOLOSolver(this.range.intValue(), this.restriction, active, aborter);
                // this will only work soundly if for all rules l -> r,
                // all variables in r also occur at least once in l.
                Pair<Set<Rule>, Map<Rule, QActiveCondition>> prRules = QDPNegPoloSolver.toRules(P, R);
                if (prRules == null) {
                    return null;
                }
                return solver.solve(prRules.x, prRules.y, allstrict);
            }
            else {
                return null;
            }
        }
    }

    private static Pair<Set<Rule>, Map<Rule, QActiveCondition>> toRules(Set<? extends GeneralizedRule> p,
        Map<? extends GeneralizedRule, QActiveCondition> r) {
        Set<Rule> pRes = new LinkedHashSet<>();
        for (GeneralizedRule genRule : p) {
            if (genRule instanceof Rule) {
                pRes.add((Rule) genRule);
            } else if (Rule.checkProperLandR(genRule.getLeft(), genRule.getRight())) {
                Rule rule = Rule.fromGeneralizedRule(genRule);
                pRes.add(rule);
            } else {
                QDPNegPoloSolver.log.fine("Dynamic NegPolo solver refuses to solve for " + genRule + " with extra vars on rhs!");
                return null;
            }
        }
        Map<Rule, QActiveCondition> rRes = new LinkedHashMap<>();
        for (Map.Entry<? extends GeneralizedRule, QActiveCondition> genRuleToCond : r.entrySet()) {
            GeneralizedRule genRule = genRuleToCond.getKey();
            if (genRule instanceof Rule) {
                rRes.put((Rule) genRule, genRuleToCond.getValue());
            } else if (Rule.checkProperLandR(genRule.getLeft(), genRule.getRight())) {
                Rule rule = Rule.fromGeneralizedRule(genRule);
                rRes.put(rule, genRuleToCond.getValue());
            } else {
                QDPNegPoloSolver.log.fine("Dynamic NegPolo solver refuses to solve for " + genRule + " with extra vars on rhs!");
                return null;
            }
        }
        return new Pair<>(pRes, rRes);
    }

    @Override
    public Pair<? extends ExportableOrder<TRSTerm>, Set<Variable<AfsProp>>> solve(Set<Pair<TRSTerm, TRSTerm>> P, Collection<Pair<? extends GeneralizedRule, Variable<AfsProp>>> R, Formula<AfsProp> sidecondition, boolean allstrict, Abortion aborter) throws AbortionException {
        assert(this.engine instanceof SatEngine);
        SatEngine satEngine = (SatEngine) this.engine;
        return NegPoloInterpretation.solve(P, R, sidecondition, this.range.abs(),
                this.posConstantRange, this.negConstantRange, allstrict,
                this.dioSatConv, satEngine, this.negRangeCriterion,
                this.partialDioEval, aborter);
    }

    @Override
    public boolean improvedSolvingSupported() {
        return this.engine instanceof SatEngine;
    }

}
