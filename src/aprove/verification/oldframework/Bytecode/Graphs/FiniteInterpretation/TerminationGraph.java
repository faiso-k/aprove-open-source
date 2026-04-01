package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.io.*;
import java.util.*;
import java.util.Map.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.*;
import java.util.concurrent.locks.ReentrantReadWriteLock.*;

import org.json.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Util.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Natives.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToGraph.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Multithread.*;

/**
 * The TerminationGraph contains all individual {@link MethodGraph}s created
 * during the construction.
 * @author fkuerten
 */
public class TerminationGraph implements Exportable {
    /**
     * Lock used to control access to the termination graph. Only threads having
     * the write lock may add/remove termination graphs. Furthermore, only
     * threads having this lock may add/remove entries to (otherwise visible)
     * NRIRs. Every running worker must have the read lock.
     */
    private final ReentrantReadWriteLock graphLock = new ReentrantReadWriteLock(true);

    /**
     * The queue holding the nodes that still need to be expanded and managing
     * the parallel processing.
     */
    private final QueueManager<MethodGraphWorker> queue;

    /**
     * The created method graphs, indexed by the corresponding method. Because
     * there may be several contexts (initialized classes etc.) we may have
     * several MethodGraphs for a single method.
     */
    private final CollectionMap<IMethod, MethodGraph> methodGraphs;

    /**
     * The options provided to the processor for this program.
     */
    private final JBCOptions jbcOptions;

    /**
     * Counter of nodes created in the TerminationGraph.
     */
    private AtomicInteger processedNodes;

    /**
     * The witness for nontermination, if one exists.
     */
    private NonTermWitness witness;

    /**
     * In debug mode, remember the static fields that are of some interest.
     */
    private final Collection<FieldIdentifier> interestingStaticFields;

    /**
     * The graphs which are locked currently.
     */
    private LinkedHashSet<MethodGraph> lockedGraphs;

    /**
     * If we change the number of availabe workers, reset them after we are
     * finished.
     */
    private int targetWorkersBefore;

    /**
     * The abortion object.
     */
    private final Abortion abortion;

    /**
     * holds representations of native methods
     */
    private final PredefinedMethodHolder predefinedMethods;

    /**
     * whether this graph contains an {@link OverflowInformation}
     */
    private boolean containsOverflows;

    /**
     * The "start" graph, i.e., the method graph that starts our analysis.
     */
    private MethodGraph startGraph;

    private HandlingMode goal;

    /**
     * Create a new and empty TerminationGraph
     * @param options the options provided to the processor
     * @param aborterParam the aborter, used to check if we still need to run
     * @throws AbortionException in case the aborter signaled us to stop
     */
    public TerminationGraph(final JBCOptions options, final HandlingMode goal, final Abortion aborterParam) throws AbortionException {
        this.processedNodes = new AtomicInteger();
        this.abortion = aborterParam;
        this.goal = goal;
        this.queue = new QueueManager<>(aborterParam, WorkStatus.FINISH);
        if (options.multithreaded) {
            final int numThreads = options.multithreadedNumThreads;
            if (numThreads != -1) {
                this.targetWorkersBefore = PrioritizableThreadPool.INSTANCE.getTargetWorkers();
                PrioritizableThreadPool.INSTANCE.setTargetWorkers(numThreads);
            }
            this.queue.setThreadingPolicy(ThreadingPolicy.LOW);
        } else if (options.pseudoMultithreaded) {
            this.queue.setThreadingPolicy(ThreadingPolicy.LOW);
        } else {
            this.queue.setThreadingPolicy(new LimitedThreadsPolicy());
        }
        if (options.parallelMerges) {
            PrioritizableThreadPool.enableReusableFeature();
        }
        this.jbcOptions = options;
        this.methodGraphs = new CollectionMap<>();
        if (Globals.DEBUG_COTTO) {
            this.interestingStaticFields = new LinkedHashSet<>();
        } else {
            this.interestingStaticFields = null;
        }
        this.predefinedMethods = new PredefinedMethodHolder(jbcOptions);
        try {
            loadPredefinedMethods();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public HandlingMode getGoal() {
        return goal;
    }

    public void loadPredefinedMethods() throws IOException {
        Optional<String> methodSummaryPath = jbcOptions.getPathToMethodSummaries();
        if (methodSummaryPath.isPresent()) {
            try {
                this.predefinedMethods.load(methodSummaryPath.get());
            } catch (JSONException e) {
                throw new RuntimeException(e);
            }
        }
    }

    /**
     * Do some checks.
     */
    public void check() {
        Collection<MethodGraph> allValues;
        this.graphLock.readLock().lock();
        try {
            allValues = this.methodGraphs.allValues();
        } finally {
            this.graphLock.readLock().unlock();
        }
        for (final MethodGraph graph : allValues) {
            graph.check();
        }
    }

    /**
     * Dump the graphs to disk.
     * @return the dump file's prefix
     */
    public String dumpImage(final boolean isFinalized) {
        if (!jbcOptions.pathToGraphDumpDirectory().isPresent()
            || (!jbcOptions.dumpIntermediateTerminationGraphs() && !isFinalized))
        {
            return null;
        }

        //Do not dump intermediate graphs for evaluation mode:
        if (!isFinalized
            && this.getJBCOptions().loopMergeCostBase == 0
            && this.getJBCOptions().loopMergeCostChange == 0)
        {
            return null;
        }

        this.graphLock.readLock().lock();
        try {
            final long nanos = System.nanoTime();
            final String path = jbcOptions.pathToGraphDumpDirectory().get();

            final File phtml = new File(path);
            if (!phtml.exists()) {
                final boolean created = phtml.mkdir();
                assert (created);
            }


            try {
                final String latest = "latest" + ".svg";
                IMethod method = this.getStartGraph().getStartNode().getState().getCurrentStackFrame().getMethod();
                String name = method.getClassName().getClassName() + "_" + method.getName();
                final String prefix = path + "/graph_" + name + "_" + nanos;
                try (BufferedWriter bw = new BufferedWriter(new FileWriter(prefix + ".txt"))) {
                    this.toDOT(bw);
                }
                if (Globals.DEBUG_COTTO) {
                    synchronized (TerminationGraph.class) {
                        Runtime.getRuntime().exec("rm " + path + "/" + latest);
                        Runtime.getRuntime().exec("ln -s " + prefix + ".svg " + path + "/" + latest);
                    }
                }
                if (Globals.DEBUG_FKUERTEN || jbcOptions.dumpIntermediateTerminationGraphs()) {
                    System.err.print("Thread "
                        + Thread.currentThread().getName()
                        + " for "
                        + this.hashCode()
                        + " dumped "
                        + prefix);
                    System.err.print("\t#graphs=" + this.methodGraphs.size());
                    for (final MethodGraph graph : this.methodGraphs.allValues()) {

                        System.err.print(" " + graph.getParsedMethod().getName() + ":" + graph.getNodeNumber() + ";");
                    }
                    System.err.println();
                }
                return prefix;
            } catch (final IOException e) {
                e.printStackTrace();
                return null;
            }
        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * Export our knowledge from the graphs.
     * @param o export util
     * @return textual representation of the graphs
     */
    @Override
    public String export(final Export_Util o) {
        final Set<Map.Entry<IMethod, Collection<MethodGraph>>> entrySet;
        this.graphLock.readLock().lock();
        try {
            entrySet = this.methodGraphs.entrySet();
        } finally {
            this.graphLock.readLock().unlock();
        }
        final StringBuilder sb = new StringBuilder();
        for (final Map.Entry<IMethod, Collection<MethodGraph>> entry : entrySet) {
            final IMethod method = entry.getKey();
            sb.append(method.getClassName());
            sb.append(".");
            sb.append(method.getName().replace("<", o.ltSign()).replace(">", o.gtSign()));
            sb.append(method.getDescriptor());
            sb.append(": ");
            for (final MethodGraph graph : entry.getValue()) {
                sb.append(graph.export(o));
                sb.append(o.newline());
            }
            sb.append(o.newline());
        }
        return sb.toString();
    }

    /**
     * Transforms this TerminationGraph into <em>one</em> dotty file containing
     * one cluster for every methodgraph.
     * @return dotty file
     * @throws IOException
     */
    public String toDOT() {
        try {
            return this.toDOT(new StringBuilder()).toString();
        } catch (IOException e) {
            //never happens for Stringbuilder
            return null;
        }
    }

    /**
     * Transforms this TerminationGraph into <em>one</em> dotty file containing
     * one cluster for every methodgraph.
     * @param sb an Appendable to append the dot String to
     * @return the Appendable
     * @throws IOException
     */
    public Appendable toDOT(final Appendable sb) throws IOException {
        sb.append("digraph dp_graph {\n"
            + "graph [mindist=0.3,nodesep=0.05,concentrate=true,ranksep=0.05];\n"
            + "node [shape=rectangle,fontsize=10,fontname=\""
            + JBCOptions.DOTTY_FONT
            + "\"];\n"
            + "edge [labeldistance=3,headclip=true,fontsize=8,fontname=\""
            + JBCOptions.DOTTY_FONT
            + "\"];\n");
        int counter = 0;

        final Map<IMethod, String> clusters = new LinkedHashMap<>();

        final LinkedHashSet<MethodGraph> myLockedGraphs = new LinkedHashSet<>();
        /*
         * Iterating over the CollectionMap is prone to ConcurrentModificationExceptions
         * Therefore we need a read lock.
         */
        this.graphLock.readLock().lock();
        try {
            // Also lock every graph
            /*
             * Unfortunately, allValues is unsuited as it uses the graphs hashCode, which depends on the graph.
             * I.e, to get allValues working correctly, we already need a readLock on each graph.
             */
            for (final Map.Entry<IMethod, Collection<MethodGraph>> entry : this.methodGraphs.entrySet()) {
                for (final MethodGraph methodGraph : entry.getValue()) {
                    methodGraph.getGraphLock().readLock().lock();
                    myLockedGraphs.add(methodGraph);
                }
            }

            // The clusters for each methodGraph
            for (final Map.Entry<IMethod, Collection<MethodGraph>> entry : this.methodGraphs.entrySet()) {
                final IMethod method = entry.getKey();
                for (final MethodGraph graph : entry.getValue()) {
                    if (TerminationGraph.skipGraph(method)) {
                        continue;
                    }
                    final String cluster = "cluster_" + counter;
                    clusters.put(method, cluster);
                    sb.append("subgraph ");
                    sb.append(cluster);
                    sb.append(" {\n");
                    sb.append("node [fontname=\"" + JBCOptions.DOTTY_FONT + "\"]");
                    sb.append("edge [fontname=\"" + JBCOptions.DOTTY_FONT + "\"]");
                    sb.append("label = \"");
                    sb.append(method.getMethodIdentifier().toString());
                    sb.append("\"\n");
                    if (method.isInstanceInitializer()) {
                        sb.append("color=");
                        sb.append(JBCOptions.COLOR_INSTANCE_INITIALIZER);
                        sb.append("; style=filled\n");
                    } else {
                        sb.append("color=");
                        sb.append(JBCOptions.COLOR_NOT_INSTANCE_INITIALIZER);
                        sb.append("\n");
                    }
                    graph.toDOTNodesAndEdges(sb);
                    sb.append("}\n");
                    counter++;
                }
            }

            // The meta edges
            // The "call" edge
            for (final Map.Entry<IMethod, Collection<MethodGraph>> entry : this.methodGraphs.entrySet()) {
                final IMethod method = entry.getKey();
                for (final MethodGraph graph : entry.getValue()) {
                    if (TerminationGraph.skipGraph(method)) {
                        continue;
                    }
                    for (final MethodEndListener l : graph.getMethodEndListeners()) {
                        boolean found = false;
                        assert (l.getMethodGraph().containsNode(l.getNode()));
                        for (final Edge edge : l.getNode().getOutEdges()) {
                            if (edge.getLabel() instanceof CallAbstractEdge) {
                                found = true;
                                Node endNode = edge.getEnd();
                                Set<Edge> outEdges = endNode.getOutEdges();
                                while (!outEdges.isEmpty()) {
                                    endNode = outEdges.iterator().next().getEnd();
                                    outEdges = endNode.getOutEdges();
                                }
                                sb.append(Integer.toString(endNode.getNodeNumber()));
                                break;
                            }
                        }
                        assert (found);
                        sb.append(" -> ");
                        sb.append(Integer.toString(graph.getStartNode().getNodeNumber()));
                        sb.append(" [color=" + JBCOptions.COLOR_METHOD_CALL + ", label=\"call\"];");
                        sb.append("\n");
                    }
                }
            }
        } finally {
            for (final MethodGraph methodGraph : myLockedGraphs) {
                methodGraph.getGraphLock().readLock().unlock();
            }
            this.graphLock.readLock().unlock();
        }

        sb.append("}\n");
        return sb;
    }

    /**
     * @param method the invoked method
     * @return true if the graph for the invoked method should not be shown
     */
    private static boolean skipGraph(final IMethod method) {
        if (!Globals.DEBUG_COTTO) {
            return false;
        }
        if (method.isInstanceInitializer() && method.getClassName().toSlashed().startsWith("java/lang/")) {
            return true;
        }
        /*
        if (method.getName().startsWith("createTree")) {
            return false;
        }
        */
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        final Set<Map.Entry<IMethod, Collection<MethodGraph>>> entrySet;
        this.graphLock.readLock().lock();
        try {
            entrySet = this.methodGraphs.entrySet();
        } finally {
            this.graphLock.readLock().unlock();
        }
        for (final Map.Entry<IMethod, Collection<MethodGraph>> entry : entrySet) {

            sb.append(entry.getKey().getMethodIdentifier());
            sb.append(": ");
            sb.append(entry.getValue().size());
            sb.append(" graphs\n");
        }
        return sb.toString();
    }

    /**
     * @return all known method graphs. Make sure that a lock is acquired or no
     * changes are made.
     */
    public CollectionMap<IMethod, MethodGraph> getMethodGraphMap() {
        this.graphLock.readLock().lock();
        try {
            return new CollectionMap<>(this.methodGraphs);
        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * @return all known method graphs.
     */
    public Collection<MethodGraph> getMethodGraphs() {
        this.graphLock.readLock().lock();
        try {
            return new LinkedHashSet<>(this.methodGraphs.allValues());
        } finally {
            this.graphLock.readLock().unlock();
        }
    }

    /**
     * Add a new method graph to this termination graph.
     * @param methodGraph the method graph to add
     */
    public void addGraph(final MethodGraph methodGraph) {
        this.methodGraphs.add(methodGraph.getParsedMethod(), methodGraph);
    }

    /**
     * Add a new method graph to this termination graph.
     * @param methodGraph the method graph to add
     */
    public void addStartGraph(final MethodGraph methodGraph) {
        assert (this.startGraph == null) : "Trying to define second start graph.";
        this.startGraph = methodGraph;
        this.addGraph(methodGraph);
    }

    /**
     * Remove parts of the individual method graphs that are not of interest
     * anymore (this is called when construction of the termination graph is
     * completed).
     */
    public void cleanUp() {
        for (final MethodGraph graph : this.methodGraphs.allValues()) {
            graph.removeUselessReturns();
        }

        if (this.getJBCOptions().retainFinishedGraphs) {
            final LinkedList<MethodGraph> todo = new LinkedList<>();
            todo.add(this.getStartGraph());
            final Collection<MethodGraph> okGraphs = new LinkedHashSet<>();
            while (!todo.isEmpty()) {
                final MethodGraph graph = todo.pop();
                if (!okGraphs.add(graph)) {
                    continue;
                }
                for (final Edge edge : graph.getEdges()) {
                    final EdgeInformation label = edge.getLabel();
                    if (label instanceof CallAbstractEdge) {
                        final Node callAbstractNode = edge.getStart();
                        for (final MethodGraph otherGraph : this.methodGraphs.allValues()) {
                            if (okGraphs.contains(otherGraph)) {
                                continue;
                            }
                            for (final MethodEndListener mel : otherGraph.getMethodEndListeners()) {
                                if (mel.getMethodGraph().equals(graph) && mel.getNode().equals(callAbstractNode)) {
                                    todo.add(otherGraph);
                                }
                            }
                        }
                    }
                }
            }

            final Collection<MethodGraph> remove = new LinkedHashSet<>();
            for (final MethodGraph graph : this.methodGraphs.allValues()) {
                if (!okGraphs.contains(graph)) {
                    remove.add(graph);
                }
            }

            for (final MethodGraph removeMe : remove) {
                this.methodGraphs.get(removeMe.getStartNode().getState().getCurrentStackFrame().getMethod()).remove(
                    removeMe);
            }
        }
    }

    /**
     * @return the options provided to the processor
     */
    public JBCOptions getJBCOptions() {
        return this.jbcOptions;
    }

    /**
     * @param result the tasks that will be added to the work queue
     * @throws AbortionException if the aborter kicks in
     */
    public synchronized void addJobs(final Collection<MethodGraphWorker> result) throws AbortionException {
        for (final MethodGraphWorker task : result) {
            if (task == null) {
                continue;
            }
            this.addJobInternal(task);
        }
    }

    /**
     * @param task the task that will be added to the work queue
     * @throws AbortionException if the aborter kicks in
     */
    private void addJobInternal(final MethodGraphWorker task) throws AbortionException {
        if (task instanceof StateNodeExpander) {
            int n = this.processedNodes.incrementAndGet();
            // Every N jobs, do some special things:
            if (n % JBCOptions.CHECK_GRAPH_EVERY_N_NODES == 0) {
                ((StateNodeExpander) task).checkGraph();;
            }
            if (n % JBCOptions.DUMP_GRAPH_EVERY_N_NODES == 0) {
                ((StateNodeExpander) task).dumpGraph();
            }
        }
        final ThreadingPolicy policy = task.getMethodGraph().getThreadingPolicy();
        this.queue.add(task, policy);
    }

    /**
     * @param task the task that will be added to the work queue
     * @throws AbortionException if the aborter kicks in
     */
    public synchronized void addJob(final MethodGraphWorker task) throws AbortionException {
        if (task == null) {
            return;
        }
        this.addJobInternal(task);
    }

    /**
     * Work on the jobs that were added in the queue and build the termination
     * graph based on that.
     * @return true if we constructed the whole termination graph
     * @throws AbortionException when the aborter kicks in
     */
    public boolean run() throws AbortionException {
        try {
            this.queue.waitForAll();
        } catch (final InterruptedException e) {
            return false;
        } finally {
            if (this.jbcOptions.multithreaded
                && this.jbcOptions.multithreadedNumThreads == PrioritizableThreadPool.INSTANCE.getTargetWorkers())
            {
                PrioritizableThreadPool.INSTANCE.setTargetWorkers(this.targetWorkersBefore);
            }
        }

        boolean acquired = false;
        try {
            // we need to lock this, because acquireAllLocks assumes the lock is held
            this.graphLock.readLock().lock();
            acquired = this.acquireAllLocks();

            if (this.queue.getHaltReason() == null || this.witness != null) {
                for (final MethodGraph mg : this.methodGraphs.allValues()) {
                    mg.dumpImage();
                }

                final String prefix = this.dumpImage(true);
                if (Globals.DEBUG_FKUERTEN || jbcOptions.pathToGraphDumpDirectory().isPresent()) {
                    System.err.println("Finished graph construction, see " + prefix);
                }
                if (jbcOptions.dumpDefaultSummaries()) {
                    predefinedMethods.dumpDefaultSummaries();
                }

                // remove parts of the graph that are not interesting anymore
                this.cleanUp();
                return true;
            }
            return false;
        } finally {
            if (acquired) {
                this.releaseAllLocks();
                this.graphLock.readLock().unlock();
            }
        }
    }

    /**
     * @param aborter an aborter
     * @return true if we can prove nontermination
     * @throws AbortionException when the aborter kicks in
     */
    public boolean runNonTermWorkers(final Abortion aborter) throws AbortionException {
        // run queued NonTerm workers
        final QueueManager<MethodGraphWorker> newQueue = new QueueManager<>(aborter, WorkStatus.FINISH);
        for (final MethodGraph mGraph : this.methodGraphs.allValues()) {
            mGraph.runNonTermWorkers(newQueue);
        }

        try {
            newQueue.waitForAll();
        } catch (final InterruptedException e) {
            return false;
        }

        return this.witness != null;
    }

    /**
     * For every call there should be at least one return state. If this is
     * missing, print out a warning (in developer mode) if we do not know about
     * that case, yet.
     * @param startState the global start state
     * @return collections of call states to which we never return and error messages
     */
    public Collection<MethodEndListener> findMissingReturns(final State startState) {
        final Collection<MethodEndListener> missing = new LinkedHashSet<>();
        for (final MethodGraph mg : this.methodGraphs.allValues()) {
            MEL: for (final MethodEndListener mel : mg.getMethodEndListeners()) {
                for (final Edge edge : mel.getNode().getOutEdges()) {
                    if (edge.getLabel() instanceof MethodSkipEdge) {
                        continue MEL;
                    }
                }
                missing.add(mel);
            }
        }

        return missing;
    }

    /**
     * @return the number of processed nodes
     */
    public AtomicInteger getProcessedNodes() {
        return this.processedNodes;
    }

    /**
     * For all NRIRs remove references to states that do not exist anymore.
     */
    public void cleanIRs() {
        final Collection<State> states = new LinkedHashSet<>();
        final Collection<MethodGraph> graphs = this.getMethodGraphs();
        for (final MethodGraph graph : graphs) {
            for (final Node node : graph.getNodes()) {
                final State state = node.getState();
                states.add(state);
            }
        }

        for (final MethodGraph graph : graphs) {
            for (final StackFrame sf : graph.getStartNode().getState().getCallStack().getStackFrameList()) {
                sf.getInputReferences().clean(states);
            }
        }
    }

    /**
     * @param w Witness for nontermination.
     */
    public void setNontermWitness(final NonTermWitness w) {
        assert (this.witness == null) : "Trying to overwrite existing nontermination witness.";
        this.witness = w;
    }

    /**
     * @return Witness for nontermination.
     */
    public NonTermWitness getNontermWitness() {
        return this.witness;
    }

    /**
     * Debugging! Remember that this field is interesting (meaning: it was read)
     * @param fieldId "ClassName.fieldName"
     */
    public void markStaticFieldAsInteresting(final FieldIdentifier fieldId) {
        if (Globals.DEBUG_COTTO) {
            this.interestingStaticFields.add(fieldId);
        }
    }

    /**
     * Debugging!
     * @param fieldId "SomeClass.fieldName"
     * @return true only for those fields that were read at least once
     * (globally!)
     */
    public boolean markedAsInterestingStaticField(final FieldIdentifier fieldId) {
        if (Globals.DEBUG_COTTO) {
            return this.interestingStaticFields.contains(fieldId);
        }
        return true;
    }

    /**
     * @return the used threading policy
     */
    public ThreadingPolicy getThreadingPolicy() {
        return this.queue.getThreadingPolicy();
    }

    /**
     * Make sure that the thread calling this method is the only working one
     * this termination graph or any method graph. The read lock for the
     * termination graph must be held upon entry.
     * @throws AbortionException when the abortion kicks in
     * @return true iff we acquired the locks (otherwise we die with an
     * exception)
     */
    public boolean acquireAllLocks() throws AbortionException {
        while (true) {
            this.abortion.checkAbortion();
            try {
                this.graphLock.readLock().unlock();
                if (this.graphLock.writeLock().tryLock() || this.graphLock.writeLock().tryLock(1, TimeUnit.SECONDS)) {
                    assert (this.lockedGraphs == null);
                    this.graphLock.readLock().lock();
                    this.lockedGraphs = new LinkedHashSet<>();
                    for (final MethodGraph mg : this.methodGraphs.allValues()) {
                        mg.getGraphLock().writeLock().lock();
                        this.lockedGraphs.add(mg);
                    }
                    assert (this.graphLock.writeLock().isHeldByCurrentThread());
                    return true;
                }
                this.graphLock.readLock().lock();
            } catch (final InterruptedException e) {
                this.graphLock.readLock().lock();
            }
        }
    }

    /**
     * Release the locks acquired using acquireAllLocks.
     */
    public void releaseAllLocks() {
        if (this.lockedGraphs != null) {
            final Iterator<MethodGraph> it = this.lockedGraphs.iterator();
            while (it.hasNext()) {
                final MethodGraph mg = it.next();
                mg.getGraphLock().writeLock().unlock();
                it.remove();
            }
            this.graphLock.writeLock().unlock();
            this.lockedGraphs = null;
        }
    }

    /**
     * Add a new graph for the given method
     * @param invokedMethod a method
     * @param newGraph a method graph
     */
    public void addMethodGraph(final IMethod invokedMethod, final MethodGraph newGraph) {
        assert (this.graphLock.writeLock().isHeldByCurrentThread());
        this.methodGraphs.add(invokedMethod, newGraph);
    }

    /**
     * @return the read lock object (which then can be (un)locked)
     */
    public ReadLock getReadLock() {
        return this.graphLock.readLock();
    }

    /**
     * @return the queue length of this lock
     */
    public int getQueueLength() {
        return this.graphLock.getQueueLength();
    }

    /**
     * @return true iff the current thread has the write lock
     */
    public boolean thisThreadHasWriteLock() {
        return this.graphLock.writeLock().isHeldByCurrentThread();
    }

    /**
     * {@link TerminationGraph#predefinedMethods}
     * @return object holding representations of native methods
     */
    public PredefinedMethodHolder getPredefinedMethods() {
        return this.predefinedMethods;
    }

    /**
     * has to be called whenever an {@link OverflowInformation} is attached to the graph
     * stores the information that overflows might occur
     */
    public void markOverflow() {
        if (!this.containsOverflows) {
            this.containsOverflows = true;
            if (Globals.DEBUG_MARC) {
                System.err.println("Overflows might occur!");
            }
        }
    }

    /**
     * @return true iff this graph contains an arithmetic computation for which we could not prove the absence of
     *  overflows.
     */
    public boolean containsOverflow() {
        return this.containsOverflows;
    }

    /**
     * @return The first graph in our analysis.
     */
    public MethodGraph getStartGraph() {
        return this.startGraph;
    }

    /**
     * @param targetGraph the method graph enclosing <code>target</code>
     * @param target some node for which we are searching a path from the start
     * @return a list of edges leading from the start state of the graph to <code>target</code>, or null if no such
     *  path could be found.
     */
    public List<Edge> getPathFromStartToNode(final MethodGraph targetGraph, final Node target) {
        //First find a list of call nodes which are leading to the graph mG. Build a graph of method graphs for that.
        //Edges are labeled with the call node:
        final SimpleGraph<MethodGraph, Node> graphGraph = new SimpleGraph<>();

        //First build nodes for all involved graphs:
        final Map<MethodGraph, aprove.verification.oldframework.Utility.Graph.Node<MethodGraph>> graphToNodeMap = new LinkedHashMap<>();
        for (final Entry<IMethod, Collection<MethodGraph>> e : this.methodGraphs.entrySet()) {
            for (final MethodGraph mG : e.getValue()) {
                final aprove.verification.oldframework.Utility.Graph.Node<MethodGraph> calledGraphNode =
                    new aprove.verification.oldframework.Utility.Graph.Node<>(mG);
                graphToNodeMap.put(mG, calledGraphNode);
                graphGraph.addNode(calledGraphNode);
            }
        }
        //Now build edges:
        for (final Entry<IMethod, Collection<MethodGraph>> e : this.methodGraphs.entrySet()) {
            for (final MethodGraph mG : e.getValue()) {
                for (final MethodEndListener mel : mG.getMethodEndListeners()) {
                    final aprove.verification.oldframework.Utility.Graph.Node<MethodGraph> start =
                        graphToNodeMap.get(mel.getMethodGraph());
                    if (start != null) {
                        graphGraph.addEdge(start, graphToNodeMap.get(mG));
                    }
                }
            }
        }

        final LinkedList<aprove.verification.oldframework.Utility.Graph.Node<MethodGraph>> graphPath =
            graphGraph.getPath(graphToNodeMap.get(this.getStartGraph()), graphToNodeMap.get(targetGraph));

        if (graphPath == null) {
            return null;
        }

        //Now build the result path:
        final List<Edge> pathFromStart = new LinkedList<>();
        MethodGraph curGraph = graphPath.removeFirst().getObject();
        while (!graphPath.isEmpty()) {
            final MethodGraph nextGraph = graphPath.removeFirst().getObject();
            //Find connection from current graph to next graph by searching for a fitting call site:
            findCallSiteLoop: for (final MethodEndListener mel : nextGraph.getMethodEndListeners()) {
                if (mel.getMethodGraph().equals(curGraph)) {
                    final Set<List<Edge>> paths =
                        JBCGraph.getAllPathsBetween(
                            curGraph.getStartNode(),
                            mel.getNode(),
                            NonTermWorker.getEdgeFilter(curGraph));
                    if (paths.isEmpty()) {
                        return null;
                    }
                    pathFromStart.addAll(paths.iterator().next());
                    //Find the call:
                    for (final Edge outEdge : mel.getNode().getOutEdges()) {
                        if (outEdge.getLabel() instanceof CallAbstractEdge) {
                            //Add the call abstract edge and the instance edge leading to the next graph:
                            pathFromStart.add(outEdge);
                            pathFromStart.add(new Edge(outEdge.getEnd(), new InstanceEdgeBetweenGraphs(), nextGraph
                                .getStartNode()));

                            //Set values anew and go on to the next graph:
                            curGraph = nextGraph;
                            break findCallSiteLoop;
                        }
                    }
                }
            }
        }
        //pathFromStart now ends at the start node of targetGraph. Now complete:
        if (targetGraph.getStartNode().equals(target)) {
            return pathFromStart;
        } else {
            final Set<List<Edge>> pathsFromGraphStartToNode =
                JBCGraph.getAllPathsBetween(
                    targetGraph.getStartNode(),
                    target,
                    NonTermWorker.getEdgeFilter(targetGraph));
            //Weird. Usually target is the old start state which was removed by now:
            if (pathsFromGraphStartToNode.isEmpty()) {
                return null;
            }

            pathFromStart.addAll(pathsFromGraphStartToNode.iterator().next());
        }

        return pathFromStart;
    }

    /**
     * @throws AbortionException {@link Abortion#checkAbortion()}
     */
    void checkAbortion() throws AbortionException {
        this.abortion.checkAbortion();
    }

    public JSONObject toJSON() throws JSONException {
        if (this.methodGraphs.size() > 1) {
            throw new NotYetImplementedException("JSON export of termination graphs with several method graphs.");
        }
        return this.getMethodGraphs().iterator().next().toJSON();
    }

}
