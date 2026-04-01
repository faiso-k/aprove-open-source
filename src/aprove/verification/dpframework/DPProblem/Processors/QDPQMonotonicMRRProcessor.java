package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Rule Removal processor for innermost(-like) rewriting.
 *
 * Using a reduction pair, tries to orient all rules of P and R
 * non-strictly and at least one rule of P or R strictly, then
 * deletes the strictly oriented rules.
 *
 * Opposed to the related MRRProcessor, here we do not require
 * full strong monotonicity. Instead, it suffices if we make sure
 * that the deleted rules can only be invoked in strongly monotonic
 * contexts. This usually requires strong monotonicity of the order
 * on /some/ argument positions, but not on all of them.
 *
 * TODO some kind of active?
 *
 * @author Carsten Fuhs
 */
public class QDPQMonotonicMRRProcessor extends QDPProblemProcessor {

    private final SolverFactory factory;
    private final boolean deleteROnly;

    @ParamsViaArgumentObject
    public QDPQMonotonicMRRProcessor(final Arguments arguments) {
        this.factory = arguments.order;
        this.deleteROnly = arguments.deleteROnly;
    }

    /* (non-Javadoc)
     * @see aprove.verification.dpframework.DPProblem.Processors.QDPProblemProcessor#processQDPProblem(aprove.verification.dpframework.DPProblem.QDPProblem, aprove.strategies.Abortions.Abortion)
     */
    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter)
            throws AbortionException {

        final Map<FunctionSymbol, MonotonicityConstraints> monReqs =
            QDPQMonotonicMRRProcessor.computeMonotonicityRequirements(qdp, aborter);
        aborter.checkAbortion();
        final OrderCalculator orderCalc = this.factory.getOrderCalculator();

        final Set<Rule> allRules = new LinkedHashSet<Rule>();
        allRules.addAll(qdp.getR());
        allRules.addAll(qdp.getP());

        final Set<Rule> deletionCandidates = this.deleteROnly ? qdp.getR() : allRules;
        final Set<Set<Rule>> dnf = this.toDNF(deletionCandidates);
        final Triple<ImmutableSet<Rule>,MonotonicityConstraints,PartiallyMonotonicOrder> rulesMonOrder =
            orderCalc.calculateStrictRulesAndMonotonicity(allRules, deletionCandidates, dnf, monReqs, aborter);

        return this.getResult(rulesMonOrder, monReqs, qdp, aborter);
    }


    /**
     * Checks whether some rules in R or P of qdp are oriented strictly
     * by solvingOrder, removes them and generates an according proof.
     *
     * Requires that solvingOrder orients all rules of P and R in qdp at least
     * non-strictly.
     *
     * @param rulesMonOrder:
     *  - the strictly oriented rules f(...) -> ... where monReqs
     *    for f are fulfilled
     *  - the constraints that the order actually fulfills
     *  - the order which is supposed to orient all rules in P united with R
     *    non-strictly and at least 1 rule f(...) -> ... strictly with monReqs
     *    for f fulfilled
     * @param qdp the QDPProblem to simplify
     * @param aborter
     * @return the corresponding result
     */
    private Result getResult(
            final Triple<ImmutableSet<Rule>,MonotonicityConstraints,PartiallyMonotonicOrder> rulesMonOrder,
            final Map<FunctionSymbol, MonotonicityConstraints> monReqs,
            final QDPProblem qdp,
            final Abortion aborter) throws AbortionException {
        if (rulesMonOrder == null) {
            return ResultFactory.unsuccessful("No suitably monotonic order found.");
        }

        final ImmutableSet<Rule> strictAndSuitablyMonotonicRules = rulesMonOrder.x;
        //MonotonicityConstraints orderMC = rulesMonOrder.y;
        final PartiallyMonotonicOrder solvingOrder = rulesMonOrder.z;

        ImmutableSet<Rule> pRules, rRules;
        pRules = qdp.getP();
        rRules = qdp.getR();

        // check which elements of P or R have been oriented strictly
        Set<Rule> newPRules, deletedPRules, newRRules, deletedRRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        newRRules = new LinkedHashSet<Rule>();
        deletedRRules = new LinkedHashSet<Rule>();
        for (final Rule rule : pRules) {
            aborter.checkAbortion();
            if (this.deleteROnly) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                            rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newPRules.add(rule);
            }
            else {
                // only add non-strictly oriented rules
                if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                    if (Globals.useAssertions) {
                        Constraint<TRSTerm> constraint;
                        constraint = Constraint.create(rule.getLeft(),
                                rule.getRight(), OrderRelation.GE);
                        assert (solvingOrder.solves(constraint));
                    }
                    newPRules.add(rule);
                }
                else {
                    deletedPRules.add(rule);
                }
            }
        }
        for (final Rule rule : rRules) {
            // only add non-strictly oriented rules
            if (! solvingOrder.inRelation(rule.getLeft(), rule.getRight())) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> constraint;
                    constraint = Constraint.create(rule.getLeft(),
                            rule.getRight(), OrderRelation.GE);
                    assert (solvingOrder.solves(constraint));
                }
                newRRules.add(rule);
            }
            else {
                final MonotonicityConstraints monReq = monReqs.get(rule.getRootSymbol());
                if (monReq.isSatisfiedBy(solvingOrder)) {
                    deletedRRules.add(rule);
                }
                else {
                    newRRules.add(rule);
                }
            }
        }

        if (Globals.useAssertions) {
            final Set<Rule> deletedRules = new LinkedHashSet<Rule>();
            deletedRules.addAll(deletedPRules);
            deletedRules.addAll(deletedRRules);
            assert ! deletedRules.isEmpty();
            //assert strictAndSuitablyMonotonicRules.containsAll(deletedRules);
        }

        // build smaller subproblem and the proof
        // different cases to be able to reuse some computed results of the current qdp problem
        QDPProblem newQdp;
        if (deletedRRules.isEmpty()) {
            newQdp = qdp.getSubProblem(ImmutableCreator.create(newPRules));
        } else if (deletedPRules.isEmpty()) {
            newQdp = qdp.getSubProblemWithSmallerR(ImmutableCreator.create(newRRules));
        } else {
            newQdp = qdp.getSubProblem(ImmutableCreator.create(newPRules), ImmutableCreator.create(newRRules));
        }
        final Proof proof = new QDPQMonotonicMRRProof(deletedRRules, deletedPRules, solvingOrder, qdp, newQdp);
        final Result result = ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);
        return result;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        // we currently require that Q-rewriting is at least as
        // restrictive as innermost R-rewriting; it may be possible to
        // relax this restriction further if we put tighter restrictions
        // on the set of deletion candidates
        return (!Options.certifier.isCeta() && qdp.QsupersetOfLhsR());
    }

    private Set<Set<Rule>> toDNF(final Set<Rule> rules) {
        final Set<Set<Rule>> res = new LinkedHashSet<Set<Rule>>();
        for (final Rule rule : rules) {
            res.add(Collections.<Rule>singleton(rule));
        }
        return res;
    }

    /**
     * @param qdp
     * @param aborter
     * @return monotonicity constraints for qdp such that a defined function
     *  symbols of R are mapped to the monotonicity constraints that must be
     *  fulfilled by the reduction pair that one wants to use to delete a
     *  strictly oriented R-rule f(...) -> ...
     * @throws AbortionException
     */
    private static Map<FunctionSymbol, MonotonicityConstraints>
                    computeMonotonicityRequirements(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        final ImmutableSet<Rule> rRules = qdp.getR();
        final ImmutableSet<Rule> pRules = qdp.getP();

        final MonotonicityCalculator monCalc = new MonotonicityCalculator();

        // for all defined symbols of R, now accumulate the
        // monotonicity requirements for *all* rhs's of P
        final Set<FunctionSymbol> definedSyms = qdp.getRwithQ().getDefinedSymbolsOfR();
        aborter.checkAbortion();
        final Map<FunctionSymbol, MonotonicityConstraints> res =
            new LinkedHashMap<FunctionSymbol, MonotonicityConstraints>();
        for (final FunctionSymbol f : definedSyms) {
            MonotonicityConstraints mc = MonotonicityConstraints.TRUE;
            for (final Rule pRule : pRules) {
                aborter.checkAbortion();
                final TRSTerm rhs = pRule.getRhsInStandardRepresentation();
                final MonotonicityConstraints currentMC =
                        monCalc.calculateRequirements(f, rRules, rhs);
                mc = mc.uniteWith(currentMC);
            }
            // now mc contains the data for f
            res.put(f, mc);
        }
        return res;
    }


    private static final class QDPQMonotonicMRRProof extends QDPProof {

        private final Set<Rule> orientedRRules;
        private final Set<Rule> orientedPRules;
        private final PartiallyMonotonicOrder order;
        private final QDPProblem origQDP;
        private final QDPProblem resultQDP;


        private QDPQMonotonicMRRProof (final Set<Rule> orientedRRules, final Set<Rule> orientedPRules,
                final PartiallyMonotonicOrder solvingOrder, final QDPProblem origQDP, final QDPProblem resultQDP) {
            if (Globals.useAssertions) {
                assert(! (orientedPRules.isEmpty()
                        && orientedRRules.isEmpty()));
            }
            this.orientedRRules = orientedRRules;
            this.orientedPRules = orientedPRules;
            this.order = solvingOrder;
            this.origQDP = origQDP;
            this.resultQDP = resultQDP;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) { // TODO deal with level
                result.append("By using the Q-monotonic rule removal processor with the following ordering, at least one Dependency Pair or term rewrite system rule of this QDP problem can be strictly oriented such that it always occurs at a strongly monotonic position in a (P,Q,R)-chain.\n");
                result.append(o.cond_linebreak());
                if (! this.orientedPRules.isEmpty()) {
                    result.append("Strictly oriented dependency pairs:\n");
                    result.append(o.set(this.orientedPRules, Export_Util.RULES));
                }
                result.append(o.cond_linebreak());
                if (! this.orientedRRules.isEmpty()) {
                    result.append("Strictly oriented rules of the TRS R:\n");
                    result.append(o.set(this.orientedRRules, Export_Util.RULES));
                }
                result.append(o.cond_linebreak());
                result.append("Used ordering: ");
                result.append(o.export(this.order));
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultQDP);
            }
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }

    public static class Arguments {
        public SolverFactory order;
        public boolean deleteROnly;
    }
}
