package aprove.verification.dpframework.TRSProblem.Utility;

import java.io.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.NodeEntry.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * (Debug Outputs: DEBUG_SEBWEI)
 *
 * try to build an OutermostTerminationGraph from a given OTRSProblem which
 *          is NOT allowed to contain Rules WITH FRESH VARIABLES ON RHSs and extract
 *      QDPProblems from the Graph if the build has succeeded;
 *
 * to understand this code in detail it is urgently recommended to take a look into my diploma thesis
 *      "Outermost-Terminierung von Termersetzungssystemen"
 *
 * @author Sebastian Weise
 */

public class OutermostTerminationGraph extends
        SimpleGraph<NodeEntry, EdgeEntry> {

    // META_VAR_PREFIX and ALLQ_VAR_PREFIX have to be DIFFERENT from each other!!
    // the prefix of Metavariables
    public final static String META_VAR_PREFIX = "x";
    // the prefix of allquantified Variables
    public final static String ALLQ_VAR_PREFIX = "z";
    /*
     * the startnumber from which the index of Metavariables will be counted;
     * indices of allquantified Variables will be counted from Term.STANDARD_NUMBER
     */
    public final static int START_NUMBER = 0;
    // an Object providing useful Methods
    private final OTRSTermGraphUtils util;
    // will be set true iff the build of the Graph has failed
    private final boolean buildFailed;
    // here our Debug-Outputs will be stored
    private final String pathForDebugOutputs;
    private static final long serialVersionUID = 1L;

    // the Strategies to handle critical Metavariables
    /*
     * "Finalize": use the Ins-Rule (declined due to worse results)
     */
    public enum Strategy {
        Linearize, Finalize
    }

    /**
     * @param otrsProblem the underlying OTRSProblem; NOT allowed to contain Rules WITH FRESH VARIABLES ON RHSs!!
     * @param strategy the Strategy to handle critical Metavariables
     * @param maxNodesBeforeFinalization the maximal number of Nodes until
     *                                      we perform explicit Finalization of the Graph
     * @param useExclusionSubstitutions iff this Value is false then
     *                                      each Node will get an EMPTY Set of ExclusionSubstitutions;
     *                                      theoretically supposed to be correct but NOT proven!!
     *                                      only for testing;
     *                                      so in fact this Value should always be true!
     * @param pathForDebugOutputs here our Debug-Outputs will be stored;
     *                              needs only to be set properly if Debug-Mode is activated;
     *                              otherwise can be set arbitrarily, e.g. = ""
     */
    public OutermostTerminationGraph(final OTRSProblem otrsProblem,
            final Strategy strategy, final int maxNodesBeforeFinalization,
            final boolean useExclusionSubstitutions,
            final String pathForDebugOutputs) {

        // check Variable-Condition
        final Set<Rule> rules = new LinkedHashSet<Rule>();
        for (final GeneralizedRule actGeneralizedRule : otrsProblem.getR()) {
            if (!(actGeneralizedRule instanceof Rule)) {
                throw new IllegalArgumentException(
                    "Class OutermostTerminationGraphBuilder is only allowed to be instantiated with an OTRSProblem which only contains Rules with no fresh Variables on Rhss.");
            }
            rules.add((Rule) actGeneralizedRule);
        }

        this.util =
            new OTRSTermGraphUtils(ImmutableCreator.create(rules),
                useExclusionSubstitutions, pathForDebugOutputs);

        this.pathForDebugOutputs = pathForDebugOutputs;

        final Desktop desktop = new Desktop();

        // build the initial Termination-Graph
        for (final FunctionSymbol f : this.util.getDefinedSymbols()) {
            final TRSTerm t =
                this.util.getPatternTermWithFreshMetaVariables(f,
                    desktop.getToUseNext());
            final Set<TRSVariable> vars =
                new LinkedHashSet<TRSVariable>(t.getVariables());
            final Node<NodeEntry> newNode =
                new Node<NodeEntry>(new NodeEntry(NodeType.Undefined, t,
                    vars, null, this.util));
            this.addNode(newNode);
            desktop.getCountCreatedNodes().increase();
            desktop.getFront().add(newNode);
        }

        // have we already expanded the Start-Nodes?
        boolean expandedStartNodes = false;
        // are we already in the state of finalizing the Graph?
        boolean finalize = false;

        // has the build of our Graph failed?
        boolean buildFailedTemp = false;
        // the number of the current Undefined-Node where the build has failed if so
        Integer nodeNumberFailed = null;

        // relevant for Debug-Outputs
        // did we have to finalize the Graph explicitely?
        boolean explicitFinalization = false;
        // did any critical Variables occur when building the Graph?
        boolean criticalVariables = false;

        int countFinishedIterations = 0;
        while (!desktop.getFront().isEmpty()) {

            final Node<NodeEntry> actNode = desktop.getFront().poll();
            final NodeEntry actNodeEntry = actNode.getObject();

            // check whether we are in or shall switch to the Finalization phase
            if (!finalize) {
                if (!expandedStartNodes) {
                    expandedStartNodes =
                        countFinishedIterations >= this.util.getDefinedSymbols().size();
                    if (!expandedStartNodes) {
                        countFinishedIterations++;
                    }
                }
                finalize =
                    desktop.getCountCreatedNodes().getIntValue() > maxNodesBeforeFinalization
                        && expandedStartNodes;
            }

            if (!finalize) {
                if (this.tryApplyParSplitRule(actNode, desktop)) {
                    continue;
                }
                if (this.tryApplyTerminRule(actNode, desktop)) {
                    continue;
                }
                if (this.tryApplyReUseHeuristic(actNode, desktop)) {
                    continue;
                }
                if (this.tryApplyNarrowRule(actNode, desktop)) {
                    continue;
                }
                if (actNodeEntry.hasCriticalVariables()) {
                    if (aprove.Globals.DEBUG_SEBWEI) {
                        criticalVariables = true;
                    }
                    if (this.tryApplyStrategyForCriticalVariables(actNode, strategy,
                        desktop)) {
                        continue;
                    }
                }
                buildFailedTemp = true;
            } else {
                if (this.tryApplyParSplitRule(actNode, desktop)) {
                    continue;
                }
                if (this.tryApplyTerminRule(actNode, desktop)) {
                    continue;
                }
                if (aprove.Globals.DEBUG_SEBWEI) {
                    explicitFinalization = true;
                }
                if (this.tryApplyFinalizationHeuristic(actNode, desktop)) {
                    continue;
                }
                // admit possible infinite building of the Graph to avoid failure
                /*
                if (tryApplyNarrowRule(actNode, desktop)) {
                    continue;
                }
                if (actNodeEntry.hasCriticalVariables()) {
                    if (aprove.Globals.DEBUG_SEBWEI) {
                        criticalVariables = true;
                    }
                    if (tryApplyStrategyForCriticalVariables(actNode, strategy,
                        desktop)) {
                        continue;
                    }
                }
                */
                buildFailedTemp = true;
            }

            if (buildFailedTemp) {
                if (aprove.Globals.DEBUG_SEBWEI) {
                    nodeNumberFailed = actNode.getNodeNumber();
                }
                break;
            }
        }

        this.buildFailed = buildFailedTemp;

        // Debug-Outputs
        if (aprove.Globals.DEBUG_SEBWEI) {
            this.dumpImage("GRAPH");
            this.util.printDebugFile("OTRSProblem",
                otrsProblem.export(new PLAIN_Util()));
            if (this.buildFailed) {
                this.util.printDebugFile("buildFailed", "");
                this.util.printDebugFile("nodeNumberFailed:_"
                    + nodeNumberFailed, "");
            }
            if (this.util.isConstructorSystem()) {
                this.util.printDebugFile("isConstructorSystem", "");
            }
            if (criticalVariables) {
                this.util.printDebugFile("criticalVariables", "");
            }
            if (explicitFinalization) {
                this.util.printDebugFile("explicitFinalization", "");
            }
            this.util.printDebugFile(
                Integer.toString(desktop.getCountCreatedNodes().getIntValue()),
                "");
        }
    }

    public boolean getBuildFailed() {
        return this.buildFailed;
    }

    public OTRSTermGraphUtils getUtil() {
        return this.util;
    }

    /**
     * @return null if the build of the Graph has failed
     */
    public Set<QDPProblem> extractQDPProblems() {
        if (this.buildFailed) {
            return null;
        }
        final Set<QDPProblem> qdpProblems = new LinkedHashSet<QDPProblem>();
        // this will be needed to create Tuplesymbols
        final Set<FunctionSymbol> signature =
            new LinkedHashSet<FunctionSymbol>(this.util.getFunctionSymbols());
        final Map<FunctionSymbol, FunctionSymbol> defToTup =
            new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        /*
         * do we have a QDPProblem where R does not contain all Rules of our OTRSProblem?
         * relevant for Debug-Outputs
         */
        boolean haveAnEmptyR = false;
        // check each SCC
        for (final Cycle<NodeEntry> actCycle : this.getSCCs()) {

            /*
             * mark the Nodes of our SCC;
             * relevant for Debug-Outputs;
             */
            if (aprove.Globals.DEBUG_SEBWEI) {
                for (final Node<NodeEntry> actNode : actCycle) {
                    actNode.getObject().setBelongsToSCC(true);
                }
            }

            final Set<Rule> P = new LinkedHashSet<Rule>();
            Set<Rule> R = new LinkedHashSet<Rule>();
            /*
             * do we have any Narrow-Nodes with potentially reducible Variablepositions
             *      in the current SCC?
             */
            for (final Node<NodeEntry> actNode : actCycle) {
                final NodeEntry actNodeEntry = actNode.getObject();
                if (actNodeEntry.getLab() == NodeType.Narrow
                    && actNodeEntry.hasPotentiallyReducibleVariablePositions()) {
                    R = this.util.getRulesAllq();
                    break;
                }
            }
            if (aprove.Globals.DEBUG_SEBWEI && R.isEmpty()) {
                haveAnEmptyR = true;
            }
            final SimpleGraph<NodeEntry, EdgeEntry> actSubGraph =
                this.getSubGraph(actCycle);
            // check for each Node whether it can start a DP-Path
            for (final Node<NodeEntry> actNode : actCycle) {
                // has the current Node an incoming Ins- or Linearize-Edge within the current SCC?
                boolean hasIncomingInsOrLinearizeEdge = false;
                for (final Edge<EdgeEntry, NodeEntry> actInEdge : actSubGraph.getInEdges(actNode)) {
                    if (actInEdge.getObject().getIsInsEdge()
                        || actInEdge.getObject().getIsLinearizeEdge()) {
                        hasIncomingInsOrLinearizeEdge = true;
                        break;
                    }
                }
                if (!hasIncomingInsOrLinearizeEdge) {
                    continue;
                }
                /*
                 * the current Node has an incoming Ins- or Linearize-Edge within the current SCC,
                 *      so search for each possible DP-Path starting in this Node
                 *
                 * Pair.x: the current Node of our Search-Front
                 * Pair.y: the so far computed Lhs of the corresponding potential P-Rule
                 */
                final Queue<Pair<Node<NodeEntry>, TRSTerm>> front =
                    new LinkedList<Pair<Node<NodeEntry>, TRSTerm>>();
                front.add(new Pair<Node<NodeEntry>, TRSTerm>(actNode,
                    actNode.getObject().getT()));
                while (!front.isEmpty()) {
                    final Pair<Node<NodeEntry>, TRSTerm> actNodeTerm =
                        front.poll();
                    final Node<NodeEntry> actFrontNode = actNodeTerm.x;
                    final TRSTerm actPlhs = actNodeTerm.y;
                    // check all outgoing Edges of the current Node
                    /*
                     * in case we have found a DP-Path, have we already added the corresponding P-Rule?
                     *      (not to add it several times)
                     */
                    boolean addedPrule = false;
                    for (final Edge<EdgeEntry, NodeEntry> actOutEdge : actSubGraph.getOutEdges(actFrontNode)) {
                        if (actOutEdge.getObject().getIsInsEdge()
                            || actOutEdge.getObject().getIsLinearizeEdge()) {
                            /*
                             * the current outgoing Edge is an Ins- or a Linearize-Edge,
                             *      so we have a DP-Path
                             */
                            if (!addedPrule) {
                                // add the corresponding P-Rule
                                // make Tuplesymbol for Lhs
                                TRSFunctionApplication lhs =
                                    (TRSFunctionApplication) actPlhs;
                                final FunctionSymbol lhsFtuple =
                                    this.util.getTupleSymbol(
                                        lhs.getRootSymbol(), defToTup,
                                        signature);
                                lhs =
                                    TRSTerm.createFunctionApplication(
                                        lhsFtuple, lhs.getArguments());
                                // make Tuplesymbol for Rhs
                                TRSFunctionApplication rhs =
                                    (TRSFunctionApplication) actFrontNode.getObject().getT();
                                final FunctionSymbol rhsFtuple =
                                    this.util.getTupleSymbol(
                                        rhs.getRootSymbol(), defToTup,
                                        signature);
                                rhs =
                                    TRSTerm.createFunctionApplication(
                                        rhsFtuple, rhs.getArguments());
                                P.add(Rule.create(lhs, rhs));
                                addedPrule = true;
                            }
                            continue;
                        }
                        /*
                         * the current outgoing Edge is not an Ins- or a Linearize-Edge,
                         *      so we can continue searching for a DP-Path
                         */
                        front.add(new Pair<Node<NodeEntry>, TRSTerm>(
                            actOutEdge.getEndNode(),
                            actPlhs.applySubstitution(actOutEdge.getObject().getSubstitution())));
                    }
                }
            }
            qdpProblems.add(QDPProblem.create(P,
                QTRSProblem.create(ImmutableCreator.create(R)), false));
        }

        // Debug-Outputs
        if (aprove.Globals.DEBUG_SEBWEI) {
            if (qdpProblems.isEmpty()) {
                this.util.printDebugFile("noSCCs", "");
            } else {
                // print our Graph with marked SCCs
                this.dumpImage("markedSCCs");
                // print our extracted QDPProblems into a file
                final StringBuilder qdps = new StringBuilder();
                final String line =
                    "---------------------------------------------";
                for (final QDPProblem actQDPProblem : qdpProblems) {
                    qdps.append(line + "\n\n");
                    qdps.append(actQDPProblem.toString() + "\n\n");
                    qdps.append(line + "\n");
                }
                this.util.printDebugFile("QDPProblems", qdps.toString());
                if (haveAnEmptyR) {
                    this.util.printDebugFile("RisEmpty", "");
                }
            }
        }

        return qdpProblems;
    }

    /***************************************************************************
     * basic Expansion Rules and Strategies
     **************************************************************************/

    /*
     * all Rule- and Strategy-Methods in this section return
     *      true iff the corresponding application succeeded;
     * parameter "actNode" is always supposed to be an Undefined-Node
     */

    private boolean tryApplyNarrowRule(final Node<NodeEntry> actNode,
        final Desktop desktop) {
        final NodeEntry actNodeEntry = actNode.getObject();
        final TRSTerm t = actNodeEntry.getT();
        if (!(t instanceof TRSFunctionApplication)) {
            return false;
        }
        if (!this.util.getDefinedSymbols().contains(
            ((TRSFunctionApplication) t).getRootSymbol())) {
            return false;
        }
        if (actNodeEntry.hasCriticalVariables()) {
            return false;
        }
        final Set<Quadruple<Node<NodeEntry>, TRSSubstitution, Position, Rule>> childNodeSubstPosRules =
            new LinkedHashSet<Quadruple<Node<NodeEntry>, TRSSubstitution, Position, Rule>>();
        for (final Position actPosition : this.util.getNonVariablePositions(t)) {
            for (final Rule actRule : this.util.getRulesAllq()) {
                final Triple<Node<NodeEntry>, TRSSubstitution, Rule> newNodeSubstRule =
                    this.util.outermostNarrow(actNode, actPosition, actRule,
                        desktop.getToUseNext());
                if (newNodeSubstRule != null) {
                    if (!newNodeSubstRule.x.getObject().isExpandable()) {
                        return false;
                    }
                    childNodeSubstPosRules.add(new Quadruple<Node<NodeEntry>, TRSSubstitution, Position, Rule>(
                        newNodeSubstRule.x, newNodeSubstRule.y, actPosition,
                        newNodeSubstRule.z));
                }
            }
        }
        if (childNodeSubstPosRules.isEmpty()) {
            return false;
        }
        actNodeEntry.setLab(NodeType.Narrow);
        for (final Quadruple<Node<NodeEntry>, TRSSubstitution, Position, Rule> actNodeSubstPosRule : childNodeSubstPosRules) {
            final EdgeEntry newEdgeEntry =
                new EdgeEntry(actNodeSubstPosRule.x);
            newEdgeEntry.setPosition(actNodeSubstPosRule.y);
            newEdgeEntry.setRule(actNodeSubstPosRule.z);
            this.myAddNode(actNode, actNodeSubstPosRule.w, newEdgeEntry,
                desktop);
        }
        return true;
    }

    private boolean tryApplyParSplitRule(final Node<NodeEntry> actNode,
        final Desktop desktop) {
        final NodeEntry actNodeEntry = actNode.getObject();
        final TRSTerm t = actNodeEntry.getT();
        final Set<TRSVariable> vars = actNodeEntry.getVars();
        final Set<ExclusionSubstitution> substsExcl = actNodeEntry.getSubsts();
        if (!(t instanceof TRSFunctionApplication)) {
            return false;
        }
        final TRSFunctionApplication tC = (TRSFunctionApplication) t;
        final FunctionSymbol c = tC.getRootSymbol();
        if (!this.util.getConstructorsArityNonZero().contains(c)) {
            return false;
        }
        actNodeEntry.setLab(NodeType.ParSplit);
        for (int i = 1; i <= c.getArity(); i++) {
            final TRSTerm tI = tC.getArgument(i - 1);
            final Set<TRSVariable> varsI = new LinkedHashSet<TRSVariable>(vars);
            varsI.retainAll(tI.getVariables());
            final Set<ExclusionSubstitution> substsI =
                this.util.extract(tI, substsExcl);
            final Node<NodeEntry> newNode =
                new Node<NodeEntry>(new NodeEntry(NodeType.Undefined, tI,
                    varsI, substsI, this.util));
            final EdgeEntry newEdgeEntry = new EdgeEntry();
            newEdgeEntry.setPosition(Position.create(new int[] { i - 1 }));
            this.myAddNode(actNode, newNode, newEdgeEntry, desktop);
        }
        return true;
    }

    private boolean tryApplyLinearizeRule(final Node<NodeEntry> actNode,
        final Desktop desktop) {

        final NodeEntry actNodeEntry = actNode.getObject();
        final TRSTerm t = actNodeEntry.getT();

        final Set<Position> positions =
            new LinkedHashSet<Position>(
                actNode.getObject().getCriticalVariablePositions());
        positions.retainAll(actNodeEntry.getPotentiallyReduciblePositions());

        // some assertions
        if (aprove.Globals.useAssertions) {
            assert (!positions.isEmpty());
        }

        if (!(t instanceof TRSFunctionApplication)) {
            return false;
        }
        if (!this.util.getDefinedSymbols().contains(
            ((TRSFunctionApplication) t).getRootSymbol())) {
            return false;
        }
        if (!actNodeEntry.hasCriticalVariables()) {
            return false;
        }
        actNodeEntry.setLab(NodeType.Linearize);
        actNodeEntry.setPositionsLinearize(positions);
        final Node<NodeEntry> childNode =
            this.util.linearize(actNode, positions, desktop.getToUseNext());
        final EdgeEntry childEdgeEntry = new EdgeEntry();
        childEdgeEntry.setIsLinearizeEdge(true);
        this.addEdge(actNode, childNode, childEdgeEntry);
        desktop.getCountCreatedNodes().increase();

        // some assertions
        if (aprove.Globals.useAssertions) {
            assert (!childNode.getObject().hasCriticalVariables());
        }

        if (this.tryApplyTerminRule(childNode, desktop)) {
            return true;
        }
        if (this.tryApplyNarrowRule(childNode, desktop)) {
            return true;
        }
        this.removeNode(childNode);
        desktop.getCountCreatedNodes().decrease();
        actNodeEntry.setLab(NodeType.Undefined);
        actNodeEntry.setPositionsLinearize(null);
        return false;
    }

    private boolean tryApplyTerminRule(final Node<NodeEntry> actNode,
        final Desktop desktop) {
        final NodeEntry actNodeEntry = actNode.getObject();
        final TRSTerm t = actNodeEntry.getT();
        if (t instanceof TRSFunctionApplication) {
            if (this.util.getConstructorsArityNonZero().contains(
                ((TRSFunctionApplication) t).getRootSymbol())) {
                return false;
            }
            if (actNodeEntry.hasCriticalVariables()) {
                return false;
            }
        }
        if (!actNodeEntry.outermostNarrowingFails(desktop.getToUseNext())) {
            return false;
        }
        actNodeEntry.setLab(NodeType.Termin);
        return true;
    }

    /**
     * applies the Ins-Rule WITHOUT checking for real applicability,
     *      so the method "checkInsRuleApplicable(...)" below must have been executed before!
     *
     * @param childNodes the corresponding Set of new Undefined-Childnodes
     *                      returned from the method "checkInsRuleApplicable(...)" below
     */
    private void applyInsRule(final Node<NodeEntry> actNode,
        final Node<NodeEntry> targetNode,
        final Set<Node<NodeEntry>> childNodes,
        final Desktop desktop) {
        actNode.getObject().setLab(NodeType.Ins);
        for (final Node<NodeEntry> currentNodeEntry : childNodes) {
            this.myAddNode(actNode, currentNodeEntry, new EdgeEntry(),
                desktop);
        }
        final EdgeEntry newEdgeEntry = new EdgeEntry();
        newEdgeEntry.setIsInsEdge(true);
        this.addEdge(actNode, targetNode, newEdgeEntry);
    }

    /**
     * @return the corresponding Set of new Undefined-Childnode-Entries (possibly empty) if
     *          the application of the Ins-Rule would succeed (without really applying it!)
     *              and null otherwise
     */
    private Set<Node<NodeEntry>> checkInsRuleApplicable(final Node<NodeEntry> actNode,
        final Node<NodeEntry> targetNode) {

        final NodeEntry actNodeEntry = actNode.getObject();
        final TRSTerm t = actNodeEntry.getT();
        final Set<TRSVariable> vars = actNodeEntry.getVars();
        final Set<ExclusionSubstitution> substsExcl = actNodeEntry.getSubsts();

        final NodeEntry targetNodeEntry = targetNode.getObject();
        final NodeType targetNodeLab = targetNodeEntry.getLab();
        final TRSTerm tTarget = targetNodeEntry.getT();
        final Set<TRSVariable> varsTarget = targetNodeEntry.getVars();
        final Set<ExclusionSubstitution> substsExclTarget =
            targetNodeEntry.getSubsts();

        if (tTarget.isVariable()) {
            return null;
        }
        if (!(targetNodeLab == NodeType.Narrow || targetNodeLab == NodeType.Termin)) {
            return null;
        }
        TRSSubstitution matcher = tTarget.getMatcher(t);
        if (matcher == null) {
            return null;
        }
        matcher = matcher.restrictTo(tTarget.getVariables());
        final Set<TRSVariable> diff = new LinkedHashSet<TRSVariable>(varsTarget);
        diff.removeAll(matcher.getDomain());
        if (!(vars.containsAll(diff))) {
            return null;
        }
        loop: for (ExclusionSubstitution substExclTarget : substsExclTarget) {
            for (ExclusionSubstitution substExcl : substsExcl) {
                if (t.applySubstitution(substExcl.getSubstitution()).getMatcher(
                    tTarget.applySubstitution(substExclTarget.getSubstitution())) != null) {
                    continue loop;
                }
            }
            return null;
        }
        final Set<Node<NodeEntry>> childNodes = new LinkedHashSet<Node<NodeEntry>>();
        for (TRSTerm tI : matcher.restrictTo(varsTarget).toMap().values()) {
            final Set<TRSVariable> varsI = new LinkedHashSet<TRSVariable>(vars);
            varsI.retainAll(tI.getVariables());
            final Set<ExclusionSubstitution> substsI = this.util.extract(tI, substsExcl);
            final NodeEntry newNodeEntry = new NodeEntry(NodeType.Undefined, tI, varsI, substsI, this.util);
            if (!newNodeEntry.isExpandable()) {
                return null;
            }
            childNodes.add(new Node<NodeEntry>(newNodeEntry));
        }
        return childNodes;
    }

    private boolean tryApplyReUseHeuristic(final Node<NodeEntry> actNode,
        final Desktop desktop) {
        Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> pairClassSCC = null;
        Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> pairClass = null;
        Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> pairGraphSCC = null;
        Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> pairGraph = null;
        Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> pairToAdd;
        final Set<Node<NodeEntry>> eqClass =
            desktop.getEquivalenceClass(actNode);
        if (eqClass != null) {
            for (final Node<NodeEntry> classNode : eqClass) {
                final Set<Node<NodeEntry>> childNodes =
                    this.checkInsRuleApplicable(actNode, classNode);
                if (childNodes == null) {
                    continue;
                }
                pairClass =
                    new Pair<Node<NodeEntry>, Set<Node<NodeEntry>>>(
                        classNode, childNodes);
                if (!this.causesSCC(actNode, classNode)) {
                    pairClassSCC = pairClass;
                    break;
                }
            }
        }
        if (pairClassSCC == null) {
            for (final Node<NodeEntry> graphNode : this.getNodes()) {
                if (actNode == graphNode) {
                    continue;
                }
                if (eqClass != null && eqClass.contains(graphNode)) {
                    continue;
                }
                if (!actNode.getObject().isEquivalent(graphNode.getObject())) {
                    continue;
                }
                final Set<Node<NodeEntry>> childNodes =
                    this.checkInsRuleApplicable(actNode, graphNode);
                if (childNodes == null) {
                    continue;
                }
                pairGraph =
                    new Pair<Node<NodeEntry>, Set<Node<NodeEntry>>>(
                        graphNode, childNodes);
                if (!this.causesSCC(actNode, graphNode)) {
                    pairGraphSCC = pairGraph;
                    break;
                }
            }
        }
        if (pairClassSCC != null) {
            pairToAdd = pairClassSCC;
        } else if (pairGraphSCC != null) {
            pairToAdd = pairGraphSCC;
        } else if (pairClass != null) {
            pairToAdd = pairClass;
        } else if (pairGraph != null) {
            pairToAdd = pairGraph;
        } else {
            return false;
        }
        if (eqClass == null) {
            desktop.createNewEquivalenceClass(pairToAdd.x);
        } else {
            if (pairToAdd != pairClassSCC && pairToAdd != pairClass) {
                eqClass.add(pairGraphSCC.x);
            }
        }
        actNode.getObject().setIsReUseNode(true);
        this.applyInsRule(actNode, pairToAdd.x, pairToAdd.y, desktop);
        return true;
    }

    private boolean tryApplyStrategyForCriticalVariables(final Node<NodeEntry> actNode,
        final Strategy strategy,
        final Desktop desktop) {
        switch (strategy) {
            case Linearize:
                if (this.tryApplyLinearizeRule(actNode, desktop)) {
                    return true;
                }
                return this.tryApplyFinalizationHeuristic(actNode, desktop);
            case Finalize:
                if (this.tryApplyFinalizationHeuristic(actNode, desktop)) {
                    return true;
                }
                return this.tryApplyLinearizeRule(actNode, desktop);
            default:
                throw new IllegalArgumentException(
                    "Undefined Value for Strategy for Critical Variables.");
        }
    }

    private boolean tryApplyFinalizationHeuristic(final Node<NodeEntry> actNode,
        final Desktop desktop) {
        Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> pairSCC = null;
        int complexitySCC = 0; // complexity of a Term is always >= 1
        Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> pair = null;
        int complexity = 0;
        Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> pairToAdd;
        for (final Node<NodeEntry> graphNode : this.getNodes()) {
            if (actNode == graphNode) {
                continue;
            }
            final Set<Node<NodeEntry>> childNodes =
                this.checkInsRuleApplicable(actNode, graphNode);
            if (childNodes == null) {
                continue;
            }
            final Pair<Node<NodeEntry>, Set<Node<NodeEntry>>> newPair =
                new Pair<Node<NodeEntry>, Set<Node<NodeEntry>>>(
                    graphNode, childNodes);
            final int newComplexity = graphNode.getObject().getComplexity();
            if (!this.causesSCC(actNode, graphNode)) {
                if (newComplexity > complexitySCC) {
                    pairSCC = newPair;
                    complexitySCC = newComplexity;
                }
            } else {
                if (newComplexity > complexity) {
                    pair = newPair;
                    complexity = newComplexity;
                }
            }
        }
        if (pairSCC != null) {
            pairToAdd = pairSCC;
        } else if (pair != null) {
            pairToAdd = pair;
        } else {
            return false;
        }
        this.applyInsRule(actNode, pairToAdd.x, pairToAdd.y, desktop);
        return true;
    }

    /***************************************************************************
     * help-methods
     **************************************************************************/

    /**
     * @param parent supposed to be a non-Undefined-Node already present in the Graph
     * @param child supposed to be a new Undefined-Node
     */
    private void myAddNode(final Node<NodeEntry> parent,
        final Node<NodeEntry> child,
        final EdgeEntry edgeEntry,
        final Desktop desktop) {
        this.addEdge(parent, child, edgeEntry);
        desktop.getCountCreatedNodes().increase();
        desktop.getFront().add(child);
    }

    /**
     * @return true iff we get an SCC by drawing an Edge from "actNode" to "targetNode"
     */
    private boolean causesSCC(final Node<NodeEntry> actNode,
        final Node<NodeEntry> targetNode) {
        return this.getPath(targetNode, actNode) != null;
    }

    /***************************************************************************
     * methods for Debug-Outputs
     **************************************************************************/

    /**
     * dumps the graph to disk
     */
    public void dumpImage(final String name) {
        final long nanos = System.nanoTime();
        FileWriter fw;
        try {
            final String base = "OTRSTerminationGraph";
            fw =
                new FileWriter(this.pathForDebugOutputs + "/" + base + nanos
                    + "_" + name + "_.txt");
            fw.write(this.myToDot());
            fw.close();
            Runtime.getRuntime().exec(
                "/usr/bin/dot -Tsvg -o " + this.pathForDebugOutputs + "/"
                    + base + nanos + "_" + name + "_.svg "
                    + this.pathForDebugOutputs + "/" + base + nanos + "_"
                    + name + "_.txt");
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * @return my beautiful DOT-Representation of the Graph
     *
     * - Node- and Edge-Entries are given
     * - NodeNumbers are given
     * - Ins-Edges are marked as dashed, red and bold
     * - Linearize-Edges are marked as dashed, green and bold
     * - Linearize-Nodes are marked as light green
     * - Ins-Nodes not used for the ReUse-Heuristic are marked as light blue
     * - Nodes to which we have applied the ReUse-Heuristic are marked as orange
     * - all other Nodes are yellow
     * - Edge-Entries are uncolored and surrounded by dashed lines
     *
     * - if Debug-Mode is activated and
     *      if the method "extractQDPProblems()" has been executed before then
     *          all Nodes lying on an SCC are marked as red!
     */
    public String myToDot() {
        final StringBuffer t = new StringBuffer("");
        t.append("digraph dp_graph {\nnode [shape=rectangle, outthreshold=100, inthreshold=100];\n");
        int maxNodeNr = 0;
        for (final Node<NodeEntry> from : this.getNodes()) {
            final int nr = from.getNodeNumber();
            if (nr > maxNodeNr) {
                maxNodeNr = nr;
            }
            t.append(nr + " [");
            if (from.getObject() != null) {
                t.append("label=\"" + from.getNodeNumber() + ": "
                    + this.getPrettyString(from.getObject()) + "\", ");
            }
            t.append("fontsize=16");

            final NodeEntry nodeEntry = from.getObject();
            final NodeType nodeType = nodeEntry.getLab();
            t.append(", style = filled, fillcolor = ");
            if (aprove.Globals.DEBUG_SEBWEI && nodeEntry.getBelongsToSCC()) {
                t.append("red");
            } else if (nodeType == NodeType.Linearize) {
                t.append("lightgreen");
            } else if (nodeEntry.getIsReUseNode()) {
                t.append("orange");
            } else if (nodeType == NodeType.Ins) {
                t.append("lightblue");
            } else {
                t.append("yellow");
            }

            t.append("];\n");
        }

        for (final Edge<EdgeEntry, NodeEntry> edge : this.getEdges()) {
            final EdgeEntry edgeEntry = edge.getObject();

            final String markEdge;
            if (edgeEntry.getIsInsEdge()) {
                markEdge = "style = \"dashed, bold\", color = red";
            } else if (edgeEntry.getIsLinearizeEdge()) {
                markEdge = "style = \"dashed, bold\", color = green";
            } else {
                markEdge = "";
            }
            final String comma =
                edgeEntry.getIsInsEdge() || edgeEntry.getIsLinearizeEdge()
                    ? ", " : "";

            maxNodeNr++;
            t.append(maxNodeNr + " [label=\"" + this.getPrettyString(edgeEntry)
                + "\", fontsize=16, style = dashed];\n");
            t.append(edge.getStartNode().getNodeNumber() + " -> " + maxNodeNr
                + " [arrowhead = none" + comma + markEdge + "];\n");
            t.append(maxNodeNr + " -> " + edge.getEndNode().getNodeNumber()
                + " [" + markEdge + "];\n\n");
        }

        return t.toString() + "}\n";
    }
}