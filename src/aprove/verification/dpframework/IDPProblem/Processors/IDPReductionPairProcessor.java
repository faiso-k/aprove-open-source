package aprove.verification.dpframework.IDPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Uses QActiveSolvers (the workhorses of the QDPReductionPair processor)
 * to find classic reduction pairs that allow to delete some rules.
 * This is most convenient if there are variables on right-hand sides of
 * rules that do not occur on left-hand sides -- a QActiveSolver can
 * determine its own argument filtering.
 *
 * Integers (and the predefined functions) could be dealt with by translation
 * to a pos-neg representation. For now, we restrict applicability to problems
 * without predefined arithmetic.
 *
 * @author Carsten Fuhs
 */
public class IDPReductionPairProcessor extends IDPProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.IDPProblem.Processors.IDPReductionPairProcessor");

    /** usable rules wrt the argument filter of the reduction pair? */
    public boolean active;

    /** orient all DPs strictly in a single go? */
    public boolean allstrict;

    /** which class of orders to search for? */
    public SolverFactory solverFactory;


    @ParamsViaArgumentObject
    public IDPReductionPairProcessor(final Arguments arguments) {
        this.active = arguments.active;
        this.allstrict = arguments.allstrict;
        this.solverFactory = arguments.order;
    }

    /** Checks if this processor is applicable to the IDP.
     *
     * At the moment, this is true for all IDP containing only integers
     * over the mathematical integers Z.
     */
    @Override
    public boolean isIDPApplicable(final IDPProblem iDP) {

        // TODO
        // Currently, we rely on sane updates to the node labels
        // by the processors and on the edge labels containing
        // (rhs(source) ->^* lhs(target)) as conjuncts to be able to switch
        // from IDP to QDP by dropping edge labels. In case some processor
        // appears in the history that does not satisfy this property, we need
        // to revise the applicability check.

        final IDPRuleAnalysis ruleA = iDP.getRuleAnalysis();
        if (ruleA.hasPredefinedDefSymbols()) {
            return false;
        }
        return true;
    }

    @Override
    protected Result processIDPProblem(final IDPProblem iDP, final Abortion aborter) throws AbortionException {

        final ImmutableSet<GeneralizedRule> idpPRules = iDP.getP();
        final ImmutableSet<GeneralizedRule> idpRRules = iDP.getR();
        final Map<GeneralizedRule, QActiveCondition> rToQAC = new LinkedHashMap<>();
        for (GeneralizedRule rule : idpRRules) {
            // TODO proper active.
            rToQAC.put(rule, QActiveCondition.TRUE);
        }
        final boolean useAllstrict = this.allstrict || idpPRules.size() == 1;
        final QActiveSolver solver = this.solverFactory.getQActiveSolver();
        final QActiveOrder order = solver.solveQActive(idpPRules, rToQAC,
            this.active, useAllstrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful();
        }

        LinkedHashSet<GeneralizedRule> newPRules = new LinkedHashSet<>();
        LinkedHashSet<GeneralizedRule> deletedPRules = new LinkedHashSet<>();
        LinkedHashSet<Node> newPNodes = new LinkedHashSet<>();
        for (final Node node : iDP.getIdpGraph().getNodes()) {
            GeneralizedRule pRule = node.rule;
            TRSTerm left = pRule.getLeft();
            TRSTerm right = pRule.getRight();
            if (! order.inRelation(left, right)) {
                if (Globals.useAssertions) {
                    Constraint<TRSTerm> lGEr = Constraint.fromRule(pRule, OrderRelation.GE);
                    assert order.solves(lGEr) : order + " does not solve " + lGEr;
                }
                newPRules.add(pRule);
                newPRules.add(node.rule);
                newPNodes.add(node);
            } else {
                deletedPRules.add(pRule);
            }
        }
        LinkedHashSet<GeneralizedRule> activeUsableRules = new LinkedHashSet<>();
        for (final Map.Entry<GeneralizedRule, QActiveCondition> entry : rToQAC.entrySet()) {
            if (order.checkQActiveCondition(entry.getValue())) {
                activeUsableRules.add(entry.getKey());
            }
        }

        if (Globals.useAssertions) {
            assert ! deletedPRules.isEmpty() : "No rule deleted!";
            for (GeneralizedRule rRule : activeUsableRules) {
                Constraint<TRSTerm> c = Constraint.fromRule(rRule, OrderRelation.GE);
                boolean oriented = order.solves(c);
                assert oriented : c + " not solved by " + order + "!";
            }
        }

        final IDPProblem newIDP = iDP.change(iDP.getIdpGraph().restrictToNodes(newPNodes, YNM.MAYBE, this), null, null, null, this);
        final IDPReductionPairProof proof = new IDPReductionPairProof(order, deletedPRules, activeUsableRules);
        return ResultFactory.proved(newIDP, YNMImplication.SOUND, proof);
    }

    public class IDPReductionPairProof extends DefaultProof {

        private final QActiveOrder order;

        private final Set<GeneralizedRule> deletedDPs;

        private final Set<GeneralizedRule> activeUsableRules;

        public IDPReductionPairProof(final QActiveOrder order, final Set<GeneralizedRule> deletedDPs,
                final Set<GeneralizedRule> activeUsableRules) {
            this.order = order;
            this.deletedDPs = deletedDPs;
            this.activeUsableRules = activeUsableRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (true) {
                result.append("We use the reduction pair processor ");
                result.append(o.cite(new Citation[]{Citation.LPAR04,Citation.JAR06}));
                result.append('.');
                result.append(o.paragraph()).append(o.cond_linebreak());
                result.append("The following pairs can be oriented strictly and are deleted.");
                result.append(o.cond_linebreak());
                result.append(o.set(this.deletedDPs, Export_Util.RULES));
                result.append("The remaining pairs can at least be oriented weakly.");
                result.append(o.linebreak());
                //result.append(o.set(this.keptPRules, Export_Util.RULES));
                result.append("Used ordering:  ");
                result.append(this.order.export(o));
                result.append(o.cond_linebreak());
                result.append("The following usable rules ");
                result.append(o.cite(Citation.FROCOS05));
                result.append(" with respect to the argument filtering of the ordering ");
                result.append(o.cite(Citation.JAR06));
                result.append(" were oriented:");
                result.append(o.cond_linebreak());
                result.append(o.set(this.activeUsableRules, Export_Util.RULES));
                result.append(o.cond_linebreak());
            }
            return result.toString();
        }
    }

    public static class Arguments {

        /** usable rules wrt the argument filter of the reduction pair? */
        public boolean active;

        /** orient all DPs strictly in a single go? */
        public boolean allstrict;

        /** which class of orders to search for? */
        public SolverFactory order;
    }
}
