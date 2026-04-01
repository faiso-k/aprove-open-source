package aprove.verification.oldframework.Bytecode;

import java.util.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.ClassInitializationInformation.*;

/**
 * This class is used for all kinds of options, processor arguments, debug
 * flags, ...
 */
public class JBCOptions {

    public static class StaticOption<T> {
        private Optional<T> t = Optional.empty();
        public void set(T t) {
            this.t = Optional.of(t);
        }
        public T get(T defaultValue) {
            return t.orElse(defaultValue);
        }
        public void reset() {
            this.t = Optional.empty();
        }
    }

    public static class InstanceOption<T> {
        private T t;
        private StaticOption<T> staticOption;
        public InstanceOption(T defaultValue, StaticOption<T> staticOption) {
            this.t = defaultValue;
            this.staticOption = staticOption;
        }
        public T get() {
            return staticOption.get(t);
        }
        public void set(T t) {
            this.t = t;
        }
    }

    /**
     * Run the checks about every CHECK_MAX nodes.
     */
    public static final int CHECK_GRAPH_EVERY_N_NODES = Integer.MAX_VALUE;

    /**
     * The color used for deleted nodes.
     */
    public static final String COLOR_DELETED = "\"#ff900\"";

    /**
     * The color used for method graphs of instance initializers ("&lt;init&gt;").
     */
    public static final String COLOR_INSTANCE_INITIALIZER = "\"#efefef\"";

    /**
     * The color used for edges connecting to the start state of a method graph.
     */
    public static final String COLOR_METHOD_CALL = "\"#6599ff\"";

    /**
     * The color used for method graphs of methods that are no instance
     * initializer ("&lt;init>").
     */
    public static final String COLOR_NOT_INSTANCE_INITIALIZER = "\"blue\"";

    /**
     * The font used for all texts in the dotty graphs.
     */
    public static final String DOTTY_FONT = "Nimbus Roman";

    /**
     * Debugging: Dump graph after this many new nodes.
     */
    public static final int DUMP_GRAPH_EVERY_N_NODES = 1000;

    /**
     * Merge chains of evaluation edges into a single edge in the DOT output.
     */
    public static final boolean MERGE_EVALS = false;

    /**
     * Merge chains of method skip edges into a single edge in the DOT output.
     */
    public static final boolean MERGE_METHODSKIPS = true;

    /**
     * If true, shows all nodes that were hidden during graph construction due to being not needed
     */
    public static final boolean SHOW_HIDDEN = false;

    /**
     * hides all static fields named serialVersionUID
     */
    public static final boolean HIDE_SERIAL_VERSION_UID = true;

    /**
     * The maximal number of (not-so-symbolic) evaluations done when verifying a
     * witness for nontermination.
     */
    public static final int MAXIMAL_WITNESS_VERIFICATION_STEPS = 1500;

    /**
     * Time in milliseconds that is allowed for each NonTermWorker task.
     */
    public static final long NONTERM_TIMEOUT = 55000;

    /**
     * If true, show a lot of debug messages when dealing with a new end state
     * (and intersecting).
     */
    public static final boolean DEBUG_METHODEND = false;

    /**
     * If true, show a lot of debug messages when dealing with delaying merges.
     */
    public static final boolean DEBUG_DELAYMERGE = false;

    /**
     * Do not add exception states to the graph-output.
     */
    public static final boolean HIDE_EXCEPTION_STATES = false;

    /**
     * If false, don't try to find states which are an instance of the new state
     * (incoming instance edges for every new state). This is not really needed
     * when just doing evaluation.
     */
    public boolean incomingInstanceFinder = true;

    /**
     * If false, don't try to find states which are more general than the new
     * state (outgoing instance edges for every new state). This is not really
     * needed when just doing evaluation and may save some time in abstract
     * graph construction.
     */
    private boolean outgoingInstanceFinder;

    /**
     * Number of loop iterations before generalization is enforced (at least 1).
     */
    private int loopMaximalIterations = 1;

    /**
     * Maximal costs of a merge after the first loop iterations.
     */
    public double loopMergeCostBase = 100.;

    /**
     * Steps in which the merge costs are changed after some loop iterations. At
     * loop iteration k < loopMaximalIterations, a merge may maximally cost
     * loopMergeCostBase + (k - 1) * loopMergeCostChange.
     */
    public double loopMergeCostChange = -20.;

    /**
     * If false, no merging is done at all.
     */
    public boolean tryMerging = true;

    /**
     * Determines if we try to split method graphs off.
     */
    public boolean trySeparateMethodAnalysis = true;

    /**
     * Determines if we try to merge parallel evaluations when encountering
     * another branching point (i.e. a refinement).
     */
    public boolean tryParallelPathMerging = true;

    /**
     * Try to do nontermination proofs.
     */
    private boolean tryNontermProofs = true;

    /**
     * Try to do looping nontermination proofs.
     */
    private boolean tryLoopingNontermProofs = true;

    /**
     * Try to do non-looping nontermination proofs.
     */
    private boolean tryNonLoopingNontermProofs = true;

    /**
     * If set, merge the states that call a method graph.
     */
    public boolean mergeCalls = false;

    /**
     * If set, detected tail calls are inlined (and the calling stack frame is
     * dropped) instead of connecting to another method graph.
     */
    public boolean inlineTailCalls = false;

    /**
     * If true, the graph construction uses multiple threads.
     */
    public boolean multithreaded = false;

    /**
     * If true, merges are done in parallel, if many need to be done at the same
     * time.
     */
    public boolean parallelMerges = false;

    /**
     * For multithreaded mode, the number of desired threads. If -1, let AProVE
     * pick. Be careful with having only one thread. Any(A, B) then behaves like
     * First(A, B).
     */
    public int multithreadedNumThreads = 4;

    /**
     * Run in parallel, but at most one job per graph.
     */
    public boolean pseudoMultithreaded = false;

    /**
     * Delay a merge until parallel paths are finished. Then do a merge with the combined information from all paths.
     */
    public boolean delayMerge = false;

    /**
     * Do stuff related to pan handle lists, cycle joints, ... (CAV paper) only if this is set.
     */
    public boolean doCycleMagic = true;

    /**
     * If true, finished graphs are kept in memory so that corresponding return states will not be deleted. This may
     * cause several graphs for a single method to exist. In unfortunate cases you may also have some finished graphes
     * that are not used anymore (if the start state is not abstract enough).
     */
    public boolean retainFinishedGraphs = false;

    public static StaticOption<Optional<String>> cliPathToMethodSummaries = new StaticOption<>();
    private InstanceOption<Optional<String>> pathToMethodSummaries = new InstanceOption<>(Optional.empty(), cliPathToMethodSummaries);

    public Optional<String> getPathToMethodSummaries() {
        return pathToMethodSummaries.get();
    }

    public void setPathToMethodSummaries(String s) {
        pathToMethodSummaries.set(Optional.of(s));
    }

    public static StaticOption<Boolean> cliSummarizeAllLibraryCalls = new StaticOption<>();
    private InstanceOption<Boolean> summarizeAllLibraryCalls = new InstanceOption<>(false, cliSummarizeAllLibraryCalls);

    public boolean summarizeAllLibraryCalls() {
        return summarizeAllLibraryCalls.get();
    }

    public void setSummarizeAllLibraryCalls(boolean b) {
        summarizeAllLibraryCalls.set(b);
    }

    public static StaticOption<Boolean> cliSummarizeRecursiveMethods = new StaticOption<>();
    private InstanceOption<Boolean> summarizeRecursiveMethods = new InstanceOption<>(false, cliSummarizeRecursiveMethods);

    public boolean summarizeRecursiveMethods() {
        return summarizeRecursiveMethods.get();
    }

    public void setSummarizeRecursiveMethods(boolean b) {
        summarizeRecursiveMethods.set(b);
    }

    /**
     * Abort the analysis of library methods where, on average, each call
     * results in more states and use a default summary instead.
     */
    public static StaticOption<Integer> cliSummarizeLibraryCallsWithMoreStates = new StaticOption<>();
    private InstanceOption<Integer> summarizeLibraryCallsWithMoreStates = new InstanceOption<>(0,  cliSummarizeLibraryCallsWithMoreStates);

    public int getSummarizeLibraryCallsWithMoreStates() {
        return summarizeLibraryCallsWithMoreStates.get();
    }

    public void setSummarizeLibraryCallsWithMoreStates(int i) {
        summarizeLibraryCallsWithMoreStates.set(i);
    }

    public static StaticOption<Boolean> cliSummarizeUnimplementedNativeMethods = new StaticOption<>();
    private InstanceOption<Boolean> summarizeUnimplementedNativeMethods = new InstanceOption<>(false, cliSummarizeUnimplementedNativeMethods);

    public boolean summarizeUnimplementedNativeMethods() {
        return summarizeUnimplementedNativeMethods.get();
    }

    public void setSummarizeUnimplementedNativeMethods(boolean b) {
        summarizeUnimplementedNativeMethods.set(b);
    }

    public static StaticOption<Boolean> cliAvoidExpandingTypeTree = new StaticOption<>();
    private InstanceOption<Boolean> avoidExpandingTypeTree = new InstanceOption<>(false, cliAvoidExpandingTypeTree);

    public boolean avoidExpandingTypeTree() {
        return avoidExpandingTypeTree.get() || dontExpandTypeTree();
    }

    public void setAvoidExpandingTypeTree(boolean b) {
        avoidExpandingTypeTree.set(b);
    }

    public static StaticOption<Boolean> cliDontExpandTypeTree = new StaticOption<>();
    private InstanceOption<Boolean> dontExpandTypeTree = new InstanceOption<>(false, cliDontExpandTypeTree);

    public boolean dontExpandTypeTree() {
        return dontExpandTypeTree.get();
    }

    public void setDontExpandTypeTree(boolean b) {
        dontExpandTypeTree.set(b);
    }

    public static StaticOption<Boolean> cliContinueOnMissingImplementations = new StaticOption<>();
    private InstanceOption<Boolean> continueOnMissingImplementations = new InstanceOption<>(false, cliContinueOnMissingImplementations);

    public boolean continueOnMissingImplementations() {
        return continueOnMissingImplementations.get();
    }

    public void setContinueOnMissingImplementations(boolean b) {
        continueOnMissingImplementations.set(b);
    }

    public static StaticOption<Boolean> cliSummarizeOnMissingImplementations = new StaticOption<>();
    private InstanceOption<Boolean> summarizeOnMissingImplementations = new InstanceOption<>(false, cliSummarizeOnMissingImplementations);

    public boolean summarizeOnMissingImplementations() {
        return summarizeOnMissingImplementations.get();
    }

    public void setSummarizeOnMissingImplementations(boolean b) {
        summarizeOnMissingImplementations.set(b);
    }

    public static StaticOption<Boolean> cliDumpDefaultSummaries = new StaticOption<>();
    private InstanceOption<Boolean> dumpDefaultSummaries = new InstanceOption<>(false, cliDumpDefaultSummaries);

    public boolean dumpDefaultSummaries() {
        return dumpDefaultSummaries.get();
    }

    public void setDumpDefaultSummaries(boolean b) {
        dumpDefaultSummaries.set(b);
    }

    public static StaticOption<Boolean> cliDumpIntermediateTerminationGraphs = new StaticOption<>();
    private InstanceOption<Boolean> dumpIntermediateTerminationGraphs = new InstanceOption<>(false, cliDumpIntermediateTerminationGraphs);

    public boolean dumpIntermediateTerminationGraphs() {
        return dumpIntermediateTerminationGraphs.get();
    }

    public void setDumpIntermediateTerminationGraphs(boolean b) {
        dumpIntermediateTerminationGraphs.set(b);
    }

    public static StaticOption<Optional<String>> cliPathToGraphDumpDirectory = new StaticOption<>();
    private InstanceOption<Optional<String>> pathToGraphDumpDirectory = new InstanceOption<>(Optional.empty(), cliPathToGraphDumpDirectory);

    public Optional<String> pathToGraphDumpDirectory() {
        return pathToGraphDumpDirectory.get();
    }

    public void setPathToGraphDumpDirectory(String s) {
        pathToGraphDumpDirectory.set(Optional.of(s));
    }

    public static StaticOption<Boolean> cliSummarizeAllMethodCalls = new StaticOption<>();
    private InstanceOption<Boolean> summarizeAllMethodCalls = new InstanceOption<>(false, cliSummarizeAllMethodCalls);

    public boolean summarizeAllMethodCalls() {
        return summarizeAllMethodCalls.get();
    }

    public void setSummarizeAllMethodCalls(boolean b) {
        summarizeAllMethodCalls.set(b);
    }

    public static StaticOption<Boolean> cliIncorrectlyBoundSizeOfConstantStringsByLength = new StaticOption<>();
    private InstanceOption<Boolean> incorrectlyBoundSizeOfConstantStringsByLength = new InstanceOption<>(false, cliIncorrectlyBoundSizeOfConstantStringsByLength);

    public boolean incorrectlyBoundSizeOfConstantStringsByLength() {
        return incorrectlyBoundSizeOfConstantStringsByLength.get();
    }

    public void setIncorrectlyBoundSizeOfConstantStringsByLength(boolean b) {
        incorrectlyBoundSizeOfConstantStringsByLength.set(b);
    }

    public static StaticOption<Boolean> cliIndicateProgress = new StaticOption<>();
    private InstanceOption<Boolean> indicateProgress = new InstanceOption<>(false, cliIndicateProgress);

    public boolean indicateProgress() {
        return indicateProgress.get();
    }

    public void setIndicateProgress(boolean b) {
        indicateProgress.set(b);
    }

    public static enum JVMBoot {
        Competition, Complete, None
    }

    public static StaticOption<JVMBoot> cliBootJVM = new StaticOption<>();
    private InstanceOption<JVMBoot> bootJVM = new InstanceOption<>(JVMBoot.None, cliBootJVM);

    public JVMBoot jvmBoot() {
        return bootJVM.get();
    }

    public void setBootJVM(JVMBoot b) {
        bootJVM.set(b);
    }

    public static StaticOption<InitStatus> cliDefaultClassInitState = new StaticOption<>();
    private InstanceOption<InitStatus> defaultClassInitState = new InstanceOption<>(InitStatus.YES, cliDefaultClassInitState);

    public InitStatus defaultClassInitState() {
        return defaultClassInitState.get();
    }

    public void setDefaultClassInitState(InitStatus s) {
        defaultClassInitState.set(s);
    }

    public static StaticOption<Boolean> cliSimplifiedStringHandling = new StaticOption<>();
    private InstanceOption<Boolean> simplifiedStringHandling = new InstanceOption<>(true, cliSimplifiedStringHandling);

    public boolean simplifiedStringHandling() {
        return simplifiedStringHandling.get();
    }

    public void setSimplifiedStringHandling(boolean b) {
        simplifiedStringHandling.set(b);
    }

    public static StaticOption<Boolean> cliSimplifiedClassHandling = new StaticOption<>();
    private InstanceOption<Boolean> simplifiedClassHandling = new InstanceOption<>(true, cliSimplifiedClassHandling);

    public boolean simplifiedClassHandling() {
        return simplifiedClassHandling.get();
    }

    public void setSimplifiedClassHandling(boolean b) {
        simplifiedClassHandling.set(b);
    }

    public static StaticOption<Boolean> cliLoadAllNativeMethods = new StaticOption<>();
    private InstanceOption<Boolean> loadAllNativeMethods = new InstanceOption<>(true, cliLoadAllNativeMethods);

    public boolean loadAllNativeMethods() {
        return loadAllNativeMethods.get();
    }

    public void setLoadAllNativeMethods(boolean b) {
        loadAllNativeMethods.set(b);
    }

    public static StaticOption<Boolean> cliInputArrayExists = new StaticOption<>();
    private InstanceOption<Boolean> inputArrayExists = new InstanceOption<>(true, cliInputArrayExists);

    public boolean inputArrayExists() {
        return inputArrayExists.get();
    }

    public void setInputArrayExists(boolean b) {
        inputArrayExists.set(b);
    }

    public static StaticOption<Optional<String>> cliDumpMethodInfoTo = new StaticOption<>();
    private InstanceOption<Optional<String>> dumpMethodInfoTo = new InstanceOption<>(Optional.empty(), cliDumpMethodInfoTo);

    public Optional<String> dumpMethodInfoTo() {
        return dumpMethodInfoTo.get();
    }

    public void setdumpMethodInfoTo(String s) {
        dumpMethodInfoTo.set(Optional.of(s));
    }

    /**
     * information about how to initialize static fields when assuming the class already was initialized
     */
    public StaticFieldInitInfo staticFieldInitInfo = new StaticFieldInitInfo();

    public void setOutgoingInstanceFinder(final boolean arg) {
        assert (arg || this.loopMaximalIterations == 1) : "See bug #76";
        this.outgoingInstanceFinder = arg;
    }

    public boolean outgoingInstanceFinder() {
        return this.outgoingInstanceFinder;
    }

    public void setLoopMaximalIterations(final int arg) {
        assert (arg > 0);
        assert (arg == 1 || arg == Integer.MAX_VALUE || this.outgoingInstanceFinder) : "See bug #76";
        this.loopMaximalIterations = arg;
    }

    public int loopMaximalIterations() {
        return this.loopMaximalIterations;
    }

    public void setTryNontermProofs(final boolean arg) {
        if (arg == false) {
            this.tryLoopingNontermProofs = false;
            this.tryNonLoopingNontermProofs = false;
        }
        this.tryNontermProofs = arg;
    }

    public boolean tryNontermProofs() {
        return this.tryNontermProofs;
    }

    public void setTryLoopingNontermProofs(boolean b) {
        this.tryLoopingNontermProofs = b;
    }

    public boolean tryLoopingNontermProofs() {
        assert (this.tryNontermProofs || !this.tryLoopingNontermProofs) : "Asked to do no non-term proofs, but looping non-term proofs. Too confused, giving up";
        return this.tryLoopingNontermProofs;
    }

    public void setTryNonLoopingNontermProofs(boolean b) {
        this.tryNonLoopingNontermProofs = b;
    }

    public boolean tryNonLoopingNontermProofs() {
        assert (this.tryNontermProofs || !this.tryNonLoopingNontermProofs) : "Asked to do no non-term proofs, but non-looping non-term proofs. Too confused, giving up";
        return this.tryNonLoopingNontermProofs;
    }

    /**
     * @param runtimeOptions runtime options, e.g. how to initialize static fields when assuming the class already was initialized
     */
    public void setRuntimeOptions(final RuntimeOptions runtimeOptions) {
        this.staticFieldInitInfo = runtimeOptions.getStaticFieldInitInfo();
    }

}
