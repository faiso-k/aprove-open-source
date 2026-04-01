package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * The PrologToPiDPTransformer builds a partial evaluation graph
 * and extracts PiDPProblems from these for which finiteness
 * guarantees termination of the PrologProgram.
 * <br><br>
 *
 * @author nowonder
 */
public class PrologToPrologProblemTransformer extends PrologProblemProcessor {

    public class PrologToPrologProblemTransformerProof extends DefaultProof implements DOT_Able {

        private final boolean exportGraph;
        private final int exportLimit;
        private final PrologEvaluationGraph petGraph;

        public PrologToPrologProblemTransformerProof(
            final PrologEvaluationGraph petGraph,
            final boolean exportGraph,
            final int exportLimit)
        {
            this.petGraph = petGraph;
            this.exportGraph = exportGraph;
            this.exportLimit = exportLimit;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            this.startUp();
            this.result.append(o.export("Built Prolog problem from termination graph "));
            this.result.append(o.export(Citation.ICLP10));
            this.result.append(o.export("."));
            this.result.append(o.newline());
            if (o instanceof HTML_Util) {
                //                if (this.petGraph.getNodes().size() <= this.exportLimit && (this.exportGraph || Options.exportGraphs)) {
                //                    try {
                //                        final Timer timer = new Timer();
                //                        timer.start();
                //                        // this code was inspired by jdotty's
                //                        // DirectedGraph.saveImage()
                //                        final IGraph g =
                //                            new DotParser(new ByteArrayInputStream(this.petGraph
                //                                .toInteractiveDOTwithEdges(true)
                //                                .getBytes()), "internal").parse().getGraph();
                //                        new Dot().layout(g, 0, 2);
                //                        final GraphPanel graphPanel = new GraphPanel(g, 1.);
                //                        final BufferedImage buf = graphPanel.getImage();
                //                        final ImageWriter imgWriter = ImageIO.getImageWritersByFormatName("png").next();
                //                        final ByteArrayOutputStream baos = new ByteArrayOutputStream();
                //                        final ImageOutputStream imgOutStream = new MemoryCacheImageOutputStream(baos);
                //                        imgWriter.setOutput(imgOutStream);
                //                        imgWriter.write(buf);
                //                        final String imgBase64 =
                //                            org.apache.commons.codec.binary.Base64.encodeBase64String(baos.toByteArray());
                //                        this.result.append("<img src=\"data:image/png;base64," + imgBase64 + "\">");
                //                        timer.stop();
                //                        if (Globals.DEBUG_CRYINGSHADOW) {
                //                            System.err.println("Exporting the graph took "
                //                                + ((int) (timer.getDuration() / 10.))
                //                                / 100.
                //                                + " sec");
                //                        }
                //                    } catch (final IOException e) {
                //                        // ignore
                //                    }
                //                } else {
                this.result.append("<textarea cols=\"80\" rows=\"25\">");
                this.result.append(this.petGraph.toInteractiveDOTwithEdges(true));
                this.result.append("</textarea>");
                //                }
            } else {
                this.result.append(o.export(this.petGraph.toInteractiveDOTwithEdges(true)));
            }
            return this.result.toString();
        }

        @Override
        public String toDOT() {
            return this.petGraph.toInteractiveDOTwithEdges(true);
        }

    }

    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologToPrologProblemTransformer");

    private static final boolean OPTIMIZE = false;

    // show graph before computing a new Prolog program
    private static final boolean PREPROCESSING_DEBUG = false;
    private final boolean exportTree;
    private final int generalizationDepth;
    private final boolean generalizeAtFirstOccurence;
    private final int maxBranchingFactor;
    private final int minNumberOfEvalSteps;
    private final boolean showTree;
    private final FrontendSMT smt;

    private final int treeLimit;

    @ParamsViaArguments(
        {
            "showTree",
            "exportTree",
            "treeLimit",
            "minNumberOfEvalSteps",
            "generalizationDepth",
            "generalizeAtFirstOccurence",
            "maxBranchingFactor",
            "smt"
        }
    )
    public PrologToPrologProblemTransformer(
        final boolean showTree,
        final boolean exportTree,
        final int treeLimit,
        final int minNumberOfEvalSteps,
        final int generalizationDepth,
        final boolean generalizeAtFirstOccurence,
        final int maxBranchingFactor,
        FrontendSMT smt
    ) {
        this.showTree = showTree;
        this.exportTree = exportTree;
        this.treeLimit = treeLimit;
        this.minNumberOfEvalSteps = minNumberOfEvalSteps;
        this.generalizationDepth = generalizationDepth;
        this.generalizeAtFirstOccurence = generalizeAtFirstOccurence;
        this.maxBranchingFactor = maxBranchingFactor;
        this.smt = smt;
    }

    public static Pair<PrologProgram, Map<FunctionSymbol, Boolean[]>> calculateProgramFromGraph(
        final PrologEvaluationGraph graph,
        final Map<Integer, String> nodeLabels,
        final Abortion aborter) throws AbortionException
    {
        final PrologProgram prog = new PrologProgram();
        final Map<FunctionSymbol, Boolean[]> groundnessFunction = (new LinkedHashMap<FunctionSymbol, Boolean[]>());
        for (final List<Node<PrologAbstractState>> path : PrologToPrologProblemTransformer.calculateAllOldClausePaths(
            graph,
            PrologToPrologProblemTransformer.OPTIMIZE,
            aborter))
        { // TODO don't use paths from left SPLIT child
          // if there is one for the right child
            final PrologClause clause =
                PrologToPrologProblemTransformer.getOldClauseFromPath(graph, path, nodeLabels, aborter);
            if (clause == null) {
                return null;
            }
            for (final FunctionSymbol pred : clause.createSetOfAllPredicates()) {
                aborter.checkAbortion();
                if (!groundnessFunction.containsKey(pred)) {
                    final Boolean[] array = new Boolean[pred.getArity()];
                    for (int i = 0; i < pred.getArity(); i++) {
                        array[i] = true;
                    }
                    groundnessFunction.put(pred, array);
                }
            }
            prog.addClause(clause.convertAbstractToNonAbstractVariables());
            final Node<PrologAbstractState> node = path.get(0);
            final KnowledgeBase kb = node.getObject().getKnowledgeBase();
            final PrologTerm t = PrologGraphProcessor.getRenamedPrologTermForNode(graph, node, false, nodeLabels);
            final Boolean[] array = groundnessFunction.get(t.createFunctionSymbol());
            for (int i = 0; i < array.length; i++) {
                if (!kb.isGround(t.getArgument(i))) {
                    array[i] = false;
                }
            }
        }
        return new Pair<PrologProgram, Map<FunctionSymbol, Boolean[]>>(prog, groundnessFunction);
    }

    public static Set<PrologProblem> calculateProgramFromGraphWithQuery(
        final PrologEvaluationGraph graph,
        final Abortion aborter) throws AbortionException
    {
        //        if (PrologToPrologProblemTransformer.PREPROCESSING_DEBUG) {
        //            graph.showNonModal();
        //        }
        final Set<PrologQuery> queries = new LinkedHashSet<PrologQuery>();
        final Map<Integer, String> nodeLabels = new LinkedHashMap<Integer, String>();
        final Pair<PrologProgram, Map<FunctionSymbol, Boolean[]>> pair =
            PrologToPrologProblemTransformer.calculateProgramFromGraph(graph, nodeLabels, aborter);
        if (pair == null) {
            return null;
        }
        final PrologProgram res = pair.x;
        if (!graph.getRoot().getObject().isEmpty()) {
            final FunctionSymbol pred =
                PrologGraphProcessor
                    .getRenamedPrologTermForNode(graph, graph.getRoot(), false, nodeLabels)
                    .createFunctionSymbol();
            if (pair.y.containsKey(pred)) {
                queries.add(new PrologQuery(pred.getName(), pair.y.get(pred), PrologPurpose.TERMINATION));
            }
        }
        // remove clauses with undefined predicates
        final List<PrologClause> clauses = res.getClauses();
        boolean removedClause = true;
        while (removedClause) {
            aborter.checkAbortion();
            removedClause = false;
            final Set<FunctionSymbol> defs = res.createSetOfDefinedPredicates();
            final Iterator<PrologClause> clauseIterator = clauses.iterator();
            while (clauseIterator.hasNext()) {
                final PrologClause clause = clauseIterator.next();
                final Set<FunctionSymbol> occs = clause.createSetOfAllPredicates();
                if (!defs.containsAll(occs)) {
                    clauseIterator.remove();
                    removedClause = true;
                }
            }
        }
        final Set<PrologProblem> returnValue = new LinkedHashSet<PrologProblem>();
        for (final PrologQuery q : queries) {
            returnValue.add(new PrologProblem(res.copy(), q, graph.getSMTFactory(), graph.getSMTLogic()));
        }
        return returnValue;
    }

    /**
     * @param aborter
     * @return
     */
    private static Set<List<Node<PrologAbstractState>>> calculateAllOldClausePaths(
        final PrologEvaluationGraph graph,
        final boolean optimize,
        final Abortion aborter)
    {
        final Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        final NodeSets sets = graph.getNodeSetsForPaths();
        for (final Node<PrologAbstractState> node : sets.getInstanceChildren()) {
            if (aborter.isAborted()) {
                return new LinkedHashSet<List<Node<PrologAbstractState>>>();
            }
            if (!graph.isRoot(node)) {
                res.addAll(PrologToPrologProblemTransformer.calculateAllOldClausePathsFromNode(
                    graph,
                    node,
                    new ArrayList<Node<PrologAbstractState>>(),
                    sets,
                    optimize,
                    aborter));
            }
        }
        for (final Node<PrologAbstractState> node : sets.getGeneralizationChildren()) {
            if (aborter.isAborted()) {
                return new LinkedHashSet<List<Node<PrologAbstractState>>>();
            }
            if (!graph.isRoot(node)) {
                res.addAll(PrologToPrologProblemTransformer.calculateAllOldClausePathsFromNode(
                    graph,
                    node,
                    new ArrayList<Node<PrologAbstractState>>(),
                    sets,
                    optimize,
                    aborter));
            }
        }
        for (final Node<PrologAbstractState> node : sets.getLeftSplitChildren()) {
            if (aborter.isAborted()) {
                return new LinkedHashSet<List<Node<PrologAbstractState>>>();
            }
            if (!graph.isRoot(node)) {
                res.addAll(PrologToPrologProblemTransformer.calculateAllOldClausePathsFromNode(
                    graph,
                    node,
                    new ArrayList<Node<PrologAbstractState>>(),
                    sets,
                    optimize,
                    aborter));
            }
        }
        if (!graph.getRoot().getObject().isEmpty()) {
            res.addAll(PrologToPrologProblemTransformer.calculateAllOldClausePathsFromNode(
                graph,
                graph.getRoot(),
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                optimize,
                aborter));
        }
        if (aborter.isAborted()) {
            return new LinkedHashSet<List<Node<PrologAbstractState>>>();
        }
        return res;
    }

    /**
     * @param node
     * @param sets
     * @param aborter
     * @return
     */
    private static Set<List<Node<PrologAbstractState>>> calculateAllOldClausePathsFromNode(
        final PrologEvaluationGraph graph,
        final Node<PrologAbstractState> node,
        final List<Node<PrologAbstractState>> currentPath,
        final NodeSets sets,
        final boolean optimize,
        final Abortion aborter)
    {
        if (aborter.isAborted()) {
            return new LinkedHashSet<List<Node<PrologAbstractState>>>();
        }
        List<Node<PrologAbstractState>> nextPath = new ArrayList<Node<PrologAbstractState>>(currentPath);
        nextPath.add(node);
        final Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        if (nextPath.size() > 1) {
            if (sets.getInstanceChildren().contains(node)
                || sets.getInstanceNodes().contains(node)
                || sets.getGeneralizationChildren().contains(node)
                || sets.getGeneralizationNodes().contains(node)
                || sets.getSuccessNodes().contains(node))
            {
                res.add(nextPath);
                nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
            }
        }
        if (nextPath.size() > 1 && sets.getLeftSplitChildren().contains(node)) {
            //            if (optimize) {
            //                Set<List<Node<PartEvalTerm>>> right =
            //                    this.calculateAllClausePathsFromNode(
            //                        this.getLastChild(node), nextPath, sets, optimize,
            //                        aborter);
            //                if (aborter.isAborted()) {
            //                    return new LinkedHashSet<List<Node<PartEvalTerm>>>();
            //                }
            //                if (right.isEmpty()) {
            //                    List<Node<PartEvalTerm>> splitPath = new ArrayList<Node<PartEvalTerm>>(nextPath);
            //                    splitPath.add(this.getFirstChild(node));
            //                    res.add(splitPath);
            //                } else {
            //                    res.addAll(right);
            //                }
            //            } else {
            final List<Node<PrologAbstractState>> splitPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
            //                splitPath.add(this.getFirstChild(node));
            res.add(splitPath);
            //                res.addAll(this.calculateAllClausePathsFromNode(
            //                    this.getLastChild(node), nextPath, sets, optimize, aborter));
            //            }
        } else if (!sets.getInstanceNodes().contains(node)
            && !sets.getGeneralizationNodes().contains(node)
            && !(nextPath.size() > 1 && (sets.getInstanceChildren().contains(node) || sets
                .getGeneralizationChildren()
                .contains(node))))
        {
            for (final Node<PrologAbstractState> child : graph.getOut(node)) {
                if (aborter.isAborted()) {
                    return new LinkedHashSet<List<Node<PrologAbstractState>>>();
                }
                res.addAll(PrologToPrologProblemTransformer.calculateAllOldClausePathsFromNode(
                    graph,
                    child,
                    nextPath,
                    sets,
                    optimize,
                    aborter));
                nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
            }
        }
        return res;
    }

    private static PrologClause getOldClauseFromPath(
        final PrologEvaluationGraph graph,
        final List<Node<PrologAbstractState>> path,
        final Map<Integer, String> nodeLabels,
        final Abortion aborter) throws AbortionException
    {
        final PrologSubstitution sigma = PrologGraphProcessor.getSubstitutionForPath(graph, path, 0, aborter);
        if (sigma == null) {
            return null;
        }
        final PrologTerm head =
            PrologGraphProcessor.getRenamedPrologTermForNode(graph, path.get(0), false, nodeLabels).applySubstitution(
                sigma);
        final PrologTerm lastBody =
            PrologGraphProcessor.getRenamedPrologTermForNode(graph, path.get(path.size() - 1), false, nodeLabels);
        final PrologTerm firstConjunct =
            PrologToPrologProblemTransformer.getOldIntermediateGoalsForClausePath(graph, path, nodeLabels, aborter);
        aborter.checkAbortion();
        final PrologTerm body = PrologTerms.createConjunction(firstConjunct, lastBody).trimTruesInConjunction();
        return new PrologClause(head, body == null ? null : body.flattenOutConjunctions());
    }

    /**
     * @param path
     * @param aborter
     * @return
     * @throws AbortionException
     */
    private static PrologTerm getOldIntermediateGoalsForClausePath(
        final PrologEvaluationGraph graph,
        final List<Node<PrologAbstractState>> path,
        final Map<Integer, String> nodeLabels,
        final Abortion aborter) throws AbortionException
    {
        if (path.size() > 1) {
            final Node<PrologAbstractState> node = path.get(0);
            final List<Node<PrologAbstractState>> restPath = new ArrayList<Node<PrologAbstractState>>();
            for (int i = 1; i < path.size(); i++) {
                restPath.add(path.get(i));
            }
            if (graph.isSplitNode(node)) {
                final Node<PrologAbstractState> child = graph.getFirstChild(node);
                if (restPath.get(0).equals(child)) {
                    return PrologToPrologProblemTransformer.getOldIntermediateGoalsForClausePath(
                        graph,
                        restPath,
                        nodeLabels,
                        aborter);
                } else {
                    //                    PrologSubstitution sigma = this.getSubstitutionForClausePath(path);
                    final PrologSubstitution sigma =
                        PrologGraphProcessor.getSubstitutionForPath(graph, path, 0, aborter);
                    //                    this.getOldSubstitutionForClausePath(path,
                    //                        new LinkedHashSet<Integer>(), aborter);
                    aborter.checkAbortion();
                    return PrologTerms.createConjunction(
                        PrologGraphProcessor
                            .getRenamedPrologTermForNode(graph, child, false, nodeLabels)
                            .applySubstitution(sigma),
                        PrologToPrologProblemTransformer.getOldIntermediateGoalsForClausePath(
                            graph,
                            restPath,
                            nodeLabels,
                            aborter)).flattenOutConjunctions();
                }
            } else {
                return PrologToPrologProblemTransformer.getOldIntermediateGoalsForClausePath(
                    graph,
                    restPath,
                    nodeLabels,
                    aborter);
            }
        } else {
            return PrologTerms.createTrue();
        }
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

    @Override
    protected Result processPrologProblem(final PrologProblem pp, final Abortion aborter) throws AbortionException {
        long time = 0;
        if (PrologToPrologProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        final GraphBuilderHeuristic petHeuristic =
            new TerminationHeuristic(
                this.minNumberOfEvalSteps,
                this.generalizationDepth,
                (this.generalizeAtFirstOccurence ? 2 : this.generalizationDepth),
                this.maxBranchingFactor);
        petHeuristic.showGraph(this.showTree);
        PrologEvaluationGraph tree = null;
        //        try {
        tree = petHeuristic.expand(pp.setSMT(this.smt), aborter);
        //        } catch (UndefinedCallException e) {
        //            return ResultFactory.notApplicable("We may reach an unknown predicate call");
        //        }
        if (PrologToPrologProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologToPrologProblemTransformer.log.log(
                Level.FINE,
                "Constructing Partial Evaluation Tree: {0}ms\n",
                time / 1000000);
            time = System.nanoTime();
        }
        if (tree == null) {
            return ResultFactory.aborted("tree construction took too long");
        }
        final Set<PrologProblem> pps =
            PrologToPrologProblemTransformer.calculateProgramFromGraphWithQuery(tree, aborter);
        if (pps == null) {
            return ResultFactory.aborted("program extraction took too long");
        }
        if (PrologToPrologProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologToPrologProblemTransformer.log.log(Level.FINE, "Reading new PrologProblem: {0}ms\n", time / 1000000);
            time = System.nanoTime();
        }
        return ResultFactory.provedAnd(pps, YNMImplication.SOUND, new PrologToPrologProblemTransformerProof(
            tree,
            this.exportTree,
            this.treeLimit));
    }

}
