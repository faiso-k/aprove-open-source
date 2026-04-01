package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * The PrologToLPTransformer builds a PrologDerivationGraph
 * and extracts a definite PrologProgram from it whose termination
 * guarantees termination of the original PrologProgram.
 * <br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */

public class PrologToLPTransformer extends PrologGraphProcessor {

    /**
     * @author cryingshadow
     * Proof for this processor.
     */
    public class PrologToLPTransformerProof extends PrologGraphProcessorProof implements DOT_Able {

        /**
         * Standard constructor.
         * @param petGraph The graph.
         * @param exportGraph Flag indicating whether to export the graph graphically.
         * @param exportLimit Limit on the number of nodes up to which the graph is exported graphically (if at all).
         * @param nodeLabels To keep the connection between the graph and the proof.
         */
        public PrologToLPTransformerProof(
            final PrologEvaluationGraph petGraph,
            final boolean exportGraph,
            final int exportLimit,
            final Map<Integer, String> nodeLabels)
        {
            super(petGraph, exportGraph, exportLimit, nodeLabels);
        }

        @Override
        protected String getProofMessage() {
            // TODO: add citation
            return "Transformed Prolog program to LP.";
        }

    }

    /**
     * Logger.
     */
    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologToLPTransformer");

    /**
     * Standard constructor.
     * @param args The arguments of this processor.
     */
    @ParamsViaArgumentObject
    public PrologToLPTransformer(final PrologOptions args) {
        super(args);
    }

    /**
     * The main method of this processor. It calculates a definite PrologProgram from the specified graph whose
     * termination implies termination of the original PrologProgram.
     * @param graph The graph to consider.
     * @param nodeLabels Mapping from node numbers to labels.
     * @param smt The SMT setting.
     * @param aborter For abortions...
     * @return The obligation returned by this processor.
     * @throws AbortionException If it is aborted...
     */
    public static PrologProblem calculateProblemFromGraph(
        final PrologEvaluationGraph graph,
        final Map<Integer, String> nodeLabels,
        final FrontendSMT smt,
        final Abortion aborter
    ) throws AbortionException {
        // construct program
        final PrologProgram prog = new PrologProgram();
        final TermNodeSets sets = graph.getTermNodeSetsForPaths(aborter);
        for (final List<Node<PrologAbstractState>> path : PrologToLPTransformer.calculateAllClausePaths(graph, sets, aborter))
        {
            prog.addClause(PrologToLPTransformer
                .getClauseFromPath(graph, path, nodeLabels, aborter)
                .convertAbstractToNonAbstractVariables());
        }
        for (final Node<PrologAbstractState> split : sets.getSplitNodes()) {
            prog.addClause(PrologToLPTransformer
                .getClauseFromSplit(split, graph, nodeLabels, aborter)
                .convertAbstractToNonAbstractVariables());
        }
        // remove clauses with undefined predicates
        final List<PrologClause> clauses = prog.getClauses();
        boolean removedClause = true;
        while (removedClause) {
            aborter.checkAbortion();
            removedClause = false;
            final Set<FunctionSymbol> defs = prog.createSetOfDefinedPredicates();
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
        // construct query
        if (!graph.getRoot().getObject().isEmpty()) {
            final PrologTerm rootTerm =
                PrologGraphProcessor.getRenamedPrologTermForNode(graph, graph.getRoot(), false, nodeLabels);
            final Boolean[] moding = new Boolean[rootTerm.getArity()];
            final KnowledgeBase kb = graph.getRoot().getObject().getKnowledgeBase();
            for (int i = 0; i < moding.length; i++) {
                if (kb.isGround(rootTerm.getArgument(i))) {
                    moding[i] = true;
                } else {
                    moding[i] = false;
                }
            }
            return
                new PrologProblem(
                    prog,
                    new PrologQuery(rootTerm.getName(), moding, PrologPurpose.TERMINATION),
                    smt.smtSolverFactory,
                    smt.smtLogic
                );
        } else {
            return new PrologProblem(prog, null, null, null);
        }
    }

    /**
     * Calculates all clause paths in the given graph. A clause path starts in the root or a successor of an instance,
     * generalization, or split node. It ends in an instance, generalization, split, or success node or the successor
     * of an instance or generalization node. It may not traverse instance, generalization, or split nodes or
     * successors of instance or generalization nodes in between.
     * @param graph The graph to consider.
     * @param sets The relevant nodes.
     * @param aborter For abortions...
     * @return The set of all clause paths in the graph.
     * @throws AbortionException If it is aborted...
     */
    private static Set<List<Node<PrologAbstractState>>> calculateAllClausePaths(
        final PrologEvaluationGraph graph,
        final TermNodeSets sets,
        final Abortion aborter) throws AbortionException
    {
        final Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        res.addAll(PrologToLPTransformer.calculateAllClausePathsFromNode(
            graph,
            graph.getRoot(),
            new ArrayList<Node<PrologAbstractState>>(),
            sets,
            aborter));
        for (final Node<PrologAbstractState> node : sets.getInstanceChildren()) {
            aborter.checkAbortion();
            res.addAll(PrologToLPTransformer.calculateAllClausePathsFromNode(
                graph,
                node,
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
        }
        for (final Node<PrologAbstractState> node : sets.getSplitNodes()) {
            aborter.checkAbortion();
            res.addAll(PrologToLPTransformer.calculateAllClausePathsFromNode(
                graph,
                graph.getFirstChild(node),
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
            res.addAll(PrologToLPTransformer.calculateAllClausePathsFromNode(
                graph,
                graph.getLastChild(node),
                new ArrayList<Node<PrologAbstractState>>(),
                sets,
                aborter));
        }
        return res;
    }

    /**
     * Calculates all clause paths in the given graph starting from the specified node with the specified currentPath
     * as prefix.
     * @param graph The graph to consider.
     * @param node The start node.
     * @param currentPath The prefix.
     * @param sets The relevant nodes.
     * @param aborter For abortions...
     * @return A set of all clause paths in the given graph starting from the specified node with the specified
     *         currentPath as prefix.
     * @throws AbortionException If it is aborted...
     */
    private static Set<List<Node<PrologAbstractState>>> calculateAllClausePathsFromNode(
        final PrologEvaluationGraph graph,
        final Node<PrologAbstractState> node,
        final List<Node<PrologAbstractState>> currentPath,
        final TermNodeSets sets,
        final Abortion aborter) throws AbortionException
    {
        aborter.checkAbortion();
        List<Node<PrologAbstractState>> nextPath = new ArrayList<Node<PrologAbstractState>>(currentPath);
        nextPath.add(node);
        final Set<List<Node<PrologAbstractState>>> res = new LinkedHashSet<List<Node<PrologAbstractState>>>();
        if (nextPath.size() > 1 && sets.getSuccessNodes().contains(node)) {
            res.add(nextPath);
            nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
        }
        if (nextPath.size() > 1 && PrologToLPTransformer.isNonSuccessEndNode(node, sets)) {
            res.add(nextPath);
        } else if (!sets.getInstanceNodes().contains(node)
            && !sets.getSplitNodes().contains(node)
            && !(nextPath.size() > 1 && sets.getInstanceChildren().contains(node)))
        {
            for (final Node<PrologAbstractState> child : graph.getOut(node)) {
                aborter.checkAbortion();
                res
                    .addAll(PrologToLPTransformer
                        .calculateAllClausePathsFromNode(graph, child, nextPath, sets, aborter));
                nextPath = new ArrayList<Node<PrologAbstractState>>(nextPath);
            }
        }
        return res;
    }

    /**
     * Constructs a clause from the given path. The first node of the path is encoded as the head of the clause while
     * the last node of the path is encoded as the body of the clause.
     * @param graph The graph containing the path.
     * @param path The path.
     * @param nodeLabels To keep the connection between graph and proof output.
     * @param aborter For abortions...
     * @return A clause simulating traversal of the given path.
     * @throws AbortionException If it is aborted...
     */
    private static PrologClause getClauseFromPath(
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
        final PrologTerm body =
            PrologGraphProcessor.getRenamedPrologTermForNode(graph, path.get(path.size() - 1), false, nodeLabels);
        aborter.checkAbortion();
        return new PrologClause(head, body.isTrue() ? null : body);
    }

    /**
     * Constructs a clause from the given split node. The split node is encoded as the head of the clause while
     * its two successors are encoded as the body of the clause.
     * @param split The split node.
     * @param graph The graph containing the split node.
     * @param nodeLabels To keep the connection between graph and proof output.
     * @param aborter For abortions...
     * @return A clause simulating traversal of the given split node.
     * @throws AbortionException If it is aborted...
     */
    private static PrologClause getClauseFromSplit(
        final Node<PrologAbstractState> split,
        final PrologEvaluationGraph graph,
        final Map<Integer, String> nodeLabels,
        final Abortion aborter) throws AbortionException
    {
        final PrologSubstitution sigma =
            PrologGraphProcessor.getAnswerSubstitution(graph.getEdgeObject(split, graph.getLastChild(split)));
        final PrologTerm head =
            PrologGraphProcessor.getRenamedPrologTermForNode(graph, split, false, nodeLabels).applySubstitution(sigma);
        final PrologTerm body1 =
            PrologGraphProcessor
                .getRenamedPrologTermForNode(graph, graph.getFirstChild(split), false, nodeLabels)
                .applySubstitution(sigma);
        final PrologTerm body2 =
            PrologGraphProcessor.getRenamedPrologTermForNode(graph, graph.getLastChild(split), false, nodeLabels);
        aborter.checkAbortion();
        return new PrologClause(head, PrologTerms.createConjunction(body1, body2));
    }

    /**
     * Checks whether the specified node is an end node, but no success node.
     * @param node The node to check.
     * @param sets The relevant nodes in the graph for the check.
     * @return True is the specified node is an end node, but no success node.
     */
    private static boolean isNonSuccessEndNode(final Node<PrologAbstractState> node, final TermNodeSets sets) {
        return sets.getInstanceChildren().contains(node)
            || sets.getInstanceNodes().contains(node)
            || sets.getSplitNodes().contains(node);
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

    @Override
    protected Logger getLogger() {
        return PrologToLPTransformer.log;
    }

    @Override
    protected Result processGraph(final PrologEvaluationGraph graph, final Abortion aborter) throws AbortionException {
        long time = 0;
        if (PrologToLPTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        //        final Set<PrologProblem> pps = new LinkedHashSet<PrologProblem>();
        final Map<Integer, String> nodeLabels = new LinkedHashMap<Integer, String>();
        final PrologProblem pp =
            PrologToLPTransformer.calculateProblemFromGraph(graph, nodeLabels, this.options.getSmt(), aborter);
        if (pp == null) {
            return ResultFactory.aborted("program extraction took too long");
        }
        //        pps.add(new PrologProblem(progFromTree));
        if (PrologToLPTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologToLPTransformer.log.log(Level.FINE, "Reading new PrologProblem: {0}ms\n", time / 1000000);
            time = System.nanoTime();
        }
        return ResultFactory
            .proved(pp, YNMImplication.SOUND, new PrologToLPTransformerProof(
                graph,
                this.options.isExportTree(),
                this.options.getTreeLimit(),
                nodeLabels));
    }

}
