package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;
import immutables.*;

/**
 * Usable Rules Reduction Pair Processor (Thm 28, LPAR 04).
 * Using a polynomial ordering, trims the TRS R to just the usable rules of P
 * and further removes all rules from R and P which contain non-usable symbols
 * of P, where the usable rules of P and P itself
 * have to be orientable non-strictly. If some rules are oriented strictly,
 * they are removed as well.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class UsableRulesReductionPairsProcessor extends AbstractPoloQDPProblemProcessor {

    private static final Logger log =
        Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.UsableRulesReductionPairsProcessor");

    private final boolean allowATrans;

    @ParamsViaArgumentObject
    public UsableRulesReductionPairsProcessor(final Arguments arguments) {
        super(arguments);
        this.allowATrans = arguments.allowATransformation && !Options.certifier.isCeta();
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        if (UsableRulesReductionPairsProcessor.log.isLoggable(Level.FINE)) {
            UsableRulesReductionPairsProcessor.log.log(Level.FINE, "Applying UsableRulesReductionPairsProcessor\n");
        }

        Set<Rule> usableRules = qdp.getUsableRules();
        Collection<Rule> P = qdp.getP();

        Pair<Map<Rule, Rule>, QTRSProblem> atransRes = null;
        if (this.allowATrans) {
            final QApplicativeUsableRules qaur = qdp.getApplicativeInfo();
            if (qaur != null) {
                atransRes = qaur.getATransformedQDP(qdp.getP(), usableRules);
                if (atransRes != null) {
                    P = atransRes.x.values();
                    usableRules = atransRes.y.getR();
                }
            }
        }

        Order<TRSTerm> solvingOrder;
        Set<Constraint<TRSTerm>> constraints;
        constraints = Constraint.fromRules(usableRules, OrderRelation.GE);
        constraints.addAll(Constraint.fromRules(P, OrderRelation.GE));

        // strong monotonicity is required here (as set by default)
        final POLOSolver solver = this.factory.getSolver(constraints);
        solver.setAllowWeakMonotonicity(false);
        solvingOrder = solver.solve(constraints, aborter);
        if (solvingOrder == null) {
            return ResultFactory.unsuccessful();
        }

        if (Globals.useAssertions) {
            for (final Constraint<TRSTerm> c : constraints) {
                assert (solvingOrder.solves(c));
            }
        }

        final Set<FunctionSymbol> usableSyms = UsableRulesReductionPairsProcessor.computeUsableSignature(P, usableRules);

        final Set<Rule> newP = new LinkedHashSet<Rule>();
        final Set<Rule> newR = new LinkedHashSet<Rule>();
        final Set<Rule> deletedP = new LinkedHashSet<Rule>(P);
        final Set<Rule> deletedR = new LinkedHashSet<Rule>(qdp.getR());
        // check whether we have happened to orient some rules strictly
        // such that we can delete them (thereby simulating a call to the
        // RuleRemovalProcessor, which would yield a significant overhead)
        for (final Rule rule : P) {
            if (!(UsableRulesReductionPairsProcessor.nonUsableSymbolInLhs(rule, usableSyms) || solvingOrder.inRelation(
                rule.getLeft(), rule.getRight()))) {
                newP.add(rule);
                deletedP.remove(rule);
            }
        }
        for (final Rule rule : usableRules) {
            if (!(UsableRulesReductionPairsProcessor.nonUsableSymbolInLhs(rule, usableSyms) || solvingOrder.inRelation(
                rule.getLeft(), rule.getRight()))) {
                newR.add(rule);
                deletedR.remove(rule);
            }
        }

        QDPProblem newQdp;
        Set<Rule> unusedAtransrules = null;
        final boolean smallerR = newR.size() < qdp.getR().size();

        // build smaller subproblem and proof
        if (atransRes == null) {
            // we did not use a-transformation
            if (deletedP.isEmpty()) {
                // we only changed the TRS R, but not P
                if (smallerR) {
                    newQdp = qdp.getSubProblemWithSmallerR(ImmutableCreator.create(newR));
                } else {
                    throw new RuntimeException("Bug in UsableRulesReductionPairsProcessor, nothing happened");
                }
            } else {
                if (smallerR) {
                    newQdp = qdp.getSubProblem(ImmutableCreator.create(newP), ImmutableCreator.create(newR));
                } else {
                    newQdp = qdp.getSubProblem(ImmutableCreator.create(newP));
                }
            }
        } else {
            // we used a-transformation, so first construct a new qtrs
            QTRSProblem newQtrs = atransRes.y;
            if (!deletedR.isEmpty()) {
                newQtrs = newQtrs.createSubProblem(ImmutableCreator.create(newR));
            }
            // and construct a new DP-graph
            final Map<Rule, Rule> ruleMap = atransRes.x;
            final Graph<Rule, ?> newGraph = new Graph<Rule, QDPProblem>();
            final Graph<Rule, ?> oldGraph = qdp.getDependencyGraph().getGraph();
            final Set<Node<Rule>> oldNodes = oldGraph.getNodes();
            final Map<Node<Rule>, Node<Rule>> nodeMap = new HashMap<Node<Rule>, Node<Rule>>(oldNodes.size());
            for (final Node<Rule> oldNode : oldNodes) {
                final Rule rule = ruleMap.get(oldNode.getObject());
                if (newP.contains(rule)) {
                    final Node<Rule> newNode = new Node<Rule>(rule);
                    nodeMap.put(oldNode, newNode);
                    newGraph.addNode(newNode);
                }
            }
            for (final Edge<?, Rule> edge : oldGraph.getEdges()) {
                final Node<Rule> newStart = nodeMap.get(edge.getStartNode());
                if (newStart != null) {
                    final Node<Rule> newEnd = nodeMap.get(edge.getEndNode());
                    if (newEnd != null) {
                        newGraph.addEdge(newStart, newEnd);
                    }
                }
            }
            newQdp = QDPProblem.create(newGraph, newQtrs, qdp.getMinimal());

            // and additionally store which rules have been deleted as they are not usable
            unusedAtransrules = new LinkedHashSet<Rule>(qdp.getR());
            unusedAtransrules.removeAll(qdp.getUsableRules());
        }
        final POLO polo = (POLO) solvingOrder;
        final Proof proof =
            new UsableRulesReductionPairsProof(deletedR, deletedP, newQdp.getR(), newQdp.getP(), usableRules, polo,
                atransRes, unusedAtransrules, qdp, newQdp);
        final Result result = ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);

        return result;
    }

    private static Set<FunctionSymbol> computeUsableSignature(final Collection<Rule> P, final Collection<Rule> U) {
        final Set<FunctionSymbol> usableSyms = new HashSet<FunctionSymbol>();
        for (final Rule rule : U) {
            rule.getRight().collectFunctionSymbols(usableSyms);
        }
        for (final Rule rule : P) {
            rule.getRight().collectFunctionSymbols(usableSyms);
        }
        return usableSyms;
    }

    private static boolean nonUsableSymbolInLhs(final Rule rule, final Set<FunctionSymbol> usableSyms) {
        for (final FunctionSymbol f : rule.getLeft().getFunctionSymbols()) {
            if (!usableSyms.contains(f)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        if (Options.certifier != Certifier.NONE && Options.certifier != Certifier.CETA && UsableRulesProcessor.checkApplicabilityConditions(qdp, true) != null) {
            return false;
        }
        return UsableRulesReductionPairsProcessor.checkApplication(qdp, this.allowATrans);
    }

    public static boolean checkApplication(final QDPProblem qdp, final boolean allowATrans) {
        if (!(qdp.getMinimal() || qdp.QsupersetOfLhsR())) {
            return false;
        }

        final Set<Rule> usable = qdp.getUsableRules();

        // check whether we can gain something
        if (usable.size() < qdp.getR().size()) {
            return true;
        }
        // okay we cannot remove non-usable rules

        // usable symbols deletion
        final Set<FunctionSymbol> usableSyms = UsableRulesReductionPairsProcessor.computeUsableSignature(qdp.getP(), usable);
        for (final FunctionSymbol f : qdp.getPRSignature()) {
            if (!usableSyms.contains(f)) {
                return true; // we can delete a rule, as the non-usable symbol f can only occur in a lhs of a rule
            }
        }

        // okay, we cannot remove rules which have non-usable symbols on their lhs.

        if (Options.certifier.isCeta()) {
            return false;
        }

        // a-transformation possible in termination case?
        if (allowATrans && !qdp.QsupersetOfLhsR() && qdp.getMaxArity() != 0) {
            final QApplicativeUsableRules qaur = qdp.getApplicativeInfo();
            if (qaur != null && qaur.getATransformedQDP(qdp.getP(), qdp.getUsableRules()) != null) {
                return true;
            }
        }

        return false;
    }

    private static final class UsableRulesReductionPairsProof extends QDPProof {
        private final Pair<Map<Rule, Rule>, QTRSProblem> atransRes; // null if not a-transformed
        private final Set<Rule> removedPRules;
        private final Set<Rule> removedRRules;
        private final Set<Rule> keptPRules;
        private final Set<Rule> keptRRules;
        private final Set<Rule> usableRules;
        private final Set<Rule> unusedAtransrules; // null if not a-transformed
        private final QDPProblem origObl;
        private final QDPProblem resultObl;
        private final POLO polo;

        private UsableRulesReductionPairsProof(final Set<Rule> removedRRules, final Set<Rule> removedPRules,
                final Set<Rule> keptRRules, final Set<Rule> keptPRules, final Set<Rule> usable, final POLO polo,
                final Pair<Map<Rule, Rule>, QTRSProblem> atransResult, final Set<Rule> unusedAtransrules,
                final QDPProblem origObl, final QDPProblem resultObl) {
            this.removedPRules = removedPRules;
            this.removedRRules = removedRRules;
            this.keptPRules = keptPRules;
            this.keptRRules = keptRRules;
            this.usableRules = usable;
            this.polo = polo;
            this.atransRes = atransResult;
            this.unusedAtransrules = unusedAtransrules;
            this.origObl = origObl;
            this.resultObl = resultObl;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            if (this.atransRes != null) {
                result.append("First, we A-transformed " + o.cite(Citation.FROCOS05) + " the QDP-Problem.\n");
                if (!this.unusedAtransrules.isEmpty()) {
                    result.append("Thereby we deleted the following non-usable rules " + o.cite(Citation.FROCOS05)
                        + ".\n");
                    result.append(o.cond_linebreak());
                    result.append(o.set(this.unusedAtransrules, Export_Util.RULES));
                    result.append(o.cond_linebreak());
                }
                result.append("Then we obtain the following A-transformed DP problem.\n");
                result.append(o.cond_linebreak());
                result.append("The pairs P are: ");
                result.append(o.cond_linebreak());
                result.append(o.set(this.atransRes.x.values(), Export_Util.RULES));
                result.append(o.cond_linebreak());
                result.append("and the Q and R are:");
                result.append(o.cond_linebreak());
                result.append(this.atransRes.y.export(o));
                result.append(o.cond_linebreak());
            }

            result.append("By using the usable rules with reduction pair processor " + o.cite(Citation.LPAR04)
                + " with a polynomial ordering " + o.cite(Citation.POLO) + ", "
                + "all dependency pairs and the corresponding usable rules " + o.cite(Citation.FROCOS05)
                + " can be oriented non-strictly.");
            result.append(" All non-usable rules are removed, and ");
            result.append("those dependency pairs and usable rules that have been oriented strictly or contain non-usable symbols in their left-hand side are removed as well.");
            result.append(o.linebreak());
            result.append(o.cond_linebreak());
            if (!this.removedPRules.isEmpty()) {
                result.append("The following dependency pairs can be deleted:");
                result.append(o.cond_linebreak());
                result.append(o.set(this.removedPRules, Export_Util.RULES));
            } else {
                result.append("No dependency pairs are removed.");
                result.append(o.linebreak());
                result.append(o.cond_linebreak());
            }
            if (!this.removedRRules.isEmpty()) {
                result.append("The following rules are removed from R:");
                result.append(o.cond_linebreak());
                result.append(o.set(this.removedRRules, Export_Util.RULES));
            } else {
                result.append("No rules are removed from R.");
                result.append(o.linebreak());
                result.append(o.cond_linebreak());
            }
            result.append("Used ordering: POLO with ");
            result.append(this.polo.export(o));
            result.append(o.cond_linebreak());
            return result.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            if (modus.isPositive()) {
                return CPFTag.DP_PROOF.create(doc,
                        CPFTag.MONO_RED_PAIR_UR_PROC.create(doc,
                                this.polo.toCPF(doc, xmlMetaData),
                                CPFTag.dps(doc, xmlMetaData, this.keptPRules),
                                CPFTag.trs(doc, xmlMetaData, this.keptRRules),
                                CPFTag.USABLE_RULES.create(doc, CPFTag.rules(doc, xmlMetaData, this.usableRules)),
                                childrenProofs[0]));
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultObl);
            }
        }

        @Override
        public String getNonCPFExportableReason(CPFModus modus) {
            return super.getNonCPFExportableReason(modus) + " with A-transformation";
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return this.atransRes == null;
        }

    }

    public static class Arguments extends AbstractPoloQDPProblemProcessor.Arguments {
        public boolean allowATransformation = true;
    }
}
