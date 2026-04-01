package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.input.Programs.triples.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * The PrologToDTProblemTransformer builds a termination graph
 * and extracts DTProblems from these for which finiteness
 * guarantees termination of the PrologProgram.
 * <br><br>
 *
 * @author cryingshadow
 */

public class PrologToDTProblemTransformer extends PrologGraphProcessor {

    public class PrologToDTProblemTransformerProof extends PrologGraphProcessorProof {

        public PrologToDTProblemTransformerProof(
            final PrologEvaluationGraph graph,
            final boolean exportGraph,
            final int exportLimit,
            final Map<Integer, String> nodeLabels)
        {
            super(graph, exportGraph, exportLimit, nodeLabels);
        }

        @Override
        protected String getProofMessage() {
            return "Built DT problem from termination graph " + Citation.DT10 + ".";
        }

    }

    private static final Logger log =
        Logger.getLogger("aprove.input.Programs.prolog.processors.PrologToDTProblemTransformer");

    /**
     * Standard constructor.
     * @param args The arguments.
     */
    @ParamsViaArgumentObject
    public PrologToDTProblemTransformer(final PrologOptions args) {
        super(args);
    }

    public static TriplesProblem calculateDTProblemFromGraph(
        final PrologEvaluationGraph graph,
        final Map<Integer, String> nodeLabels,
        final Abortion aborter) throws AbortionException
    {
        final PrologProgram triples = new PrologProgram();
        final PrologProgram program = new PrologProgram();
        final Afs afs = new Afs();
        final Map<FunctionSymbol, boolean[]> groundnessFunction = (new LinkedHashMap<FunctionSymbol, boolean[]>());
        final NodeSets sets = graph.getNodeSetsForPaths();
        for (final List<Node<PrologAbstractState>> path : PrologGraphProcessor.calculateAllClausePaths(graph, sets, aborter))
        {
            final PrologClause clause =
                PrologToDTProblemTransformer.getClauseFromPath(graph, path, nodeLabels, aborter);
            if (clause == null) {
                return null;
            }
            for (final FunctionSymbol pred : clause.createSetOfAllPredicates()) {
                aborter.checkAbortion();
                if (!groundnessFunction.containsKey(pred)) {
                    final boolean[] array = new boolean[pred.getArity()];
                    for (int i = 0; i < pred.getArity(); i++) {
                        array[i] = true;
                    }
                    groundnessFunction.put(pred, array);
                }
            }
            program.addClause(clause.convertAbstractToNonAbstractVariables().renameNonAbstractVariablesCanonically());
            final Node<PrologAbstractState> node = path.get(0);
            final KnowledgeBase kb = node.getObject().getKnowledgeBase();
            // need original variables again -
            // head of clause is already replaced!
            final PrologTerm t = PrologGraphProcessor.getRenamedPrologTermForNode(graph, node, true, nodeLabels);
            final boolean[] array = groundnessFunction.get(t.createFunctionSymbol());
            for (int i = 0; i < array.length; i++) {
                if (!kb.isGround(t.getArgument(i))) {
                    array[i] = false;
                }
            }
        }
        for (final List<Node<PrologAbstractState>> path : PrologGraphProcessor.calculateAllTriplePaths(graph, sets, aborter))
        {
            final PrologClause clause =
                PrologToDTProblemTransformer.getTripleFromPath(graph, path, nodeLabels, aborter);
            if (clause == null) {
                return null;
            }
            for (final FunctionSymbol pred : clause.createSetOfAllPredicates()) {
                aborter.checkAbortion();
                if (!groundnessFunction.containsKey(pred)) {
                    final boolean[] array = new boolean[pred.getArity()];
                    for (int i = 0; i < pred.getArity(); i++) {
                        array[i] = true;
                    }
                    groundnessFunction.put(pred, array);
                }
            }
            triples.addClause(clause.convertAbstractToNonAbstractVariables().renameNonAbstractVariablesCanonically());
            final Node<PrologAbstractState> node = path.get(0);
            final KnowledgeBase kb = node.getObject().getKnowledgeBase();
            // need original variables again -
            // head of clause is already replaced!
            final PrologTerm t = PrologGraphProcessor.getRenamedPrologTermForNode(graph, node, false, nodeLabels);
            final boolean[] array = groundnessFunction.get(t.createFunctionSymbol());
            for (int i = 0; i < array.length; i++) {
                if (!kb.isGround(t.getArgument(i))) {
                    array[i] = false;
                }
            }
        }
        if (!graph.getRoot().getObject().isEmpty()) {
            final FunctionSymbol rootNodeSymbol =
                PrologGraphProcessor
                    .getRenamedPrologTermForNode(graph, graph.getRoot(), false, nodeLabels)
                    .createFunctionSymbol();
            final boolean[] moding = groundnessFunction.get(rootNodeSymbol);
            if (moding != null) {
                afs.setFiltering(rootNodeSymbol, moding);
            }
        }
        //for (Map.Entry<FunctionSymbol, boolean[]> entry : groundnessFunction.entrySet()) {
        //afs.setFiltering(entry.getKey(), entry.getValue());
        //}
        return new TriplesProblem(triples, program, afs);
    }

    /**
     * @param graph
     * @param path
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public static PrologTerm getIntermediateGoalsForPath(
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
                    return PrologToDTProblemTransformer.getIntermediateGoalsForPath(
                        graph,
                        restPath,
                        nodeLabels,
                        aborter);
                } else {
                    final PrologSubstitution sigma =
                        PrologGraphProcessor.getSubstitutionForPath(graph, path, 0, aborter);
                    aborter.checkAbortion();
                    final PrologTerm first =
                        PrologGraphProcessor
                            .getRenamedPrologTermForNode(graph, child, true, nodeLabels)
                            .applySubstitution(sigma);
                    return PrologTerms.createConjunction(
                        first,
                        PrologToDTProblemTransformer.getIntermediateGoalsForPath(graph, restPath, nodeLabels, aborter));
                }
            } else {
                return PrologToDTProblemTransformer.getIntermediateGoalsForPath(graph, restPath, nodeLabels, aborter);
            }
        } else {
            return PrologTerms.createTrue();
        }
    }

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
            PrologGraphProcessor.getRenamedPrologTermForNode(graph, path.get(0), true, nodeLabels).applySubstitution(
                sigma);
        final PrologTerm lastBody =
            PrologGraphProcessor.getRenamedPrologTermForNode(graph, path.get(path.size() - 1), true, nodeLabels);
        final PrologTerm firstConjunct =
            PrologToDTProblemTransformer.getIntermediateGoalsForPath(graph, path, nodeLabels, aborter);
        aborter.checkAbortion();
        final PrologTerm body = PrologTerms.createConjunction(firstConjunct, lastBody).trimTruesInConjunction();
        return new PrologClause(head, body == null ? null : body.flattenOutConjunctions());
    }

    private static PrologClause getTripleFromPath(
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
            PrologToDTProblemTransformer.getIntermediateGoalsForPath(graph, path, nodeLabels, aborter);
        aborter.checkAbortion();
        final PrologTerm body = PrologTerms.createConjunction(firstConjunct, lastBody).trimTruesInConjunction();
        return new PrologClause(head, body == null ? null : body.flattenOutConjunctions());
    }

    @Override
    public boolean isPrologApplicable(final PrologProblem pp) {
        return pp.getQuery().getPurpose().equals(PrologPurpose.TERMINATION);
    }

    @Override
    protected Logger getLogger() {
        return PrologToDTProblemTransformer.log;
    }

    @Override
    protected Result processGraph(final PrologEvaluationGraph graph, final Abortion aborter) throws AbortionException {
        long time = 0;
        if (PrologToDTProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime();
        }
        final Set<TriplesProblem> pps = new LinkedHashSet<TriplesProblem>();
        final Map<Integer, String> nodeLabels = new LinkedHashMap<Integer, String>();
        final TriplesProblem problemFromGraph =
            PrologToDTProblemTransformer.calculateDTProblemFromGraph(graph, nodeLabels, aborter);
        if (problemFromGraph == null) {
            return ResultFactory.aborted("problem extraction took too long");
        }
        pps.add(problemFromGraph);
        if (PrologToDTProblemTransformer.log.isLoggable(Level.FINE)) {
            time = System.nanoTime() - time;
            PrologToDTProblemTransformer.log.log(Level.FINE, "Reading DT Problem: {0}ms\n", time / 1000000);
        }
        return ResultFactory.provedAnd(pps, YNMImplication.SOUND, new PrologToDTProblemTransformerProof(
            graph,
            this.options.isExportTree(),
            this.options.getTreeLimit(),
            nodeLabels));
    }

}
