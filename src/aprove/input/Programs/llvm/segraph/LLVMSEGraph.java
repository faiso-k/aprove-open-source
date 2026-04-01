package aprove.input.Programs.llvm.segraph;

import aprove.Globals;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.segraph.graphConstructionSteps.*;
import aprove.input.Programs.llvm.segraph.graphListeners.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.input.Programs.llvm.utils.static_analysis.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

import org.json.JSONObject;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.math.BigInteger;
import java.util.*;
import java.util.function.Predicate;

/**
 * The symbolic evaluation graph for LLVM.
 * @author Janine Repke, cryingshadow
 */
public class LLVMSEGraph extends SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> {



    /**
     * For serialization.
     */
    private static final long serialVersionUID = -628115981495597055L;


    /**
     * The graph construction step that is currently active
     */
    private LLVMAbstractGraphConstructionStep currentlyActiveStep;

    /**
     * Gives to every basic block a list of nodes whose instruction is the first within the corresponding block.
     */
    private final Map<ImmutablePair<String, String>, List<Node<LLVMAbstractState>>> blockToNode;


    @Deprecated
    private final Map<String, LinkedList<Node<LLVMAbstractState>>> fnNameToEntryNodeQueue;

    @Deprecated
    public Node<LLVMAbstractState> getCurrentEntryNodeForFunction(String functionName) {
    	if(Globals.useAssertions) {
    		assert !functionName.startsWith("@");
    	}
		LinkedList<Node<LLVMAbstractState>> previousAndCurrentEntryNodes =  fnNameToEntryNodeQueue.get(functionName);
		if(previousAndCurrentEntryNodes == null)
			return null;

		return previousAndCurrentEntryNodes.getLast();
	}


    @Deprecated
    public void setEntryNodeForFunction(String functionName, Node<LLVMAbstractState> entryNode) {
    	if(Globals.useAssertions) {
    		assert !functionName.startsWith("@");
    		assert entryNode.getObject().getCallStack().isEmpty();
    	}

    	LinkedList<Node<LLVMAbstractState>> previousAndCurrentEntryNodes =  fnNameToEntryNodeQueue.get(functionName);
		if(previousAndCurrentEntryNodes == null)
			previousAndCurrentEntryNodes = new LinkedList<>();

		previousAndCurrentEntryNodes.addLast(entryNode);
		fnNameToEntryNodeQueue.put(functionName, previousAndCurrentEntryNodes);
	}

	/*
     * Names without scope (i.e @)
     */
	@Deprecated
    private Set<String> recursiveFunctions;


	@Deprecated
    public Set<Node<LLVMAbstractState>> getCurrentAndOutdatedEntryNodesOfFunction(String recursiveFunctionName) {
    	if(Globals.useAssertions) {
    		assert !recursiveFunctionName.startsWith("@");
    		isRecursiveFunction(recursiveFunctionName);
    	}
    	LinkedList<Node<LLVMAbstractState>> previousAndCurrentEntryNodes = null;
    	if((previousAndCurrentEntryNodes = fnNameToEntryNodeQueue.get(recursiveFunctionName)) == null) {
    		return Collections.emptySet();
    	} else {
    		return new LinkedHashSet<>(previousAndCurrentEntryNodes);
    	}


    }

    /**
     * The LLVM module.
     */
    private final LLVMModule module;


    /**
     * The start node of the graph.
     */
    private Node<LLVMAbstractState> root;

    /**
     * Parameters specified by the strategy.
     */
    private final LLVMParameters strategyParameters;


    private final LinkedHashSet<LLVMAbstractGraphConstructionStep> remainingGraphConstructionSteps;

    /**
     * Nodes which still exist in the graph, but where some progenitor state has been merged (needed to achieve the
     * same behavior independent from whether or not unneeded nodes are removed from the graph - see DebuggingFlags).
     */
    private final Set<Node<LLVMAbstractState>> unneededNodes;

    private final Set<LLVMSEGraphEventListener> eventListeners;

    /**
     * Contains heuristics about which functions should be intersected
     * (in addition to recursive function, which are always intersected)
     */
    private  LLVMIntersectionHeuristics intersectionHeuristics;

    private LLVMLiveVariableAnalysis liveVariableAnalysis;

    /**
     * Contains heuristics about *when* we must merge states.
     * (not actual merging done there)
     */
    private final LLVMForceMergeHeuristic forceMergeHeuristics;

    private  LLVMFunctionGraphTracker functionGraphTracker;

    /**
     * Creates an symbolic evaluation graph for an LLVM module.
     * After calling this constructor, the graph will still be empty. Call {@link #buildFullGraph()} to create the actual graph.
     *
     * @param moduleParam The LLVM module.
     * @param query The starting query.
     * @param params Strategy parameters.
     */
    public LLVMSEGraph(LLVMModule moduleParam, LLVMQuery query, LLVMParameters params, Abortion aborter) {
        this.strategyParameters = params;
        this.blockToNode = new LinkedHashMap<ImmutablePair<String, String>, List<Node<LLVMAbstractState>>>();
        this.unneededNodes = new LinkedHashSet<Node<LLVMAbstractState>>();
        this.fnNameToEntryNodeQueue = new HashMap<>();
        this.eventListeners = new LinkedHashSet<>();
        this.recursiveFunctions = new LinkedHashSet<>();
        this.liveVariableAnalysis = new LLVMLiveVariableAnalysis();
        this.module = moduleParam.setLiveVariables(liveVariableAnalysis.getLiveVariables(moduleParam));


        initIntersectionStructures(params,moduleParam,aborter);
        this.forceMergeHeuristics = new LLVMForceMergeHeuristic(moduleParam,getIntersectionHeuristics());

        //Steps that need to be performed initially. 
        LLVMAbstractGraphConstructionStep[] initialSteps = new LLVMAbstractGraphConstructionStep[] {
        	//new LLVMRecursionDetectionStep(this),
        	new LLVMRootStateCreationStep(this,query)
        };
        this.remainingGraphConstructionSteps = new LinkedHashSet<LLVMAbstractGraphConstructionStep>(Arrays.asList(initialSteps));

        addSEGraphEventListener(new LLVMSEGraphIntegrityChecker(this));
		if (params.proveFreeOfMemoryLeaks) {
			addSEGraphEventListener(new LLVMEndStateMemoryLeakListener(this));
		}

		currentlyActiveStep = new LLVMNoopStep(this);
    }

    /**
     * Builds from the root node a full SE graph without debug output.
     * @throws MemorySafetyException If memory safety of the program cannot be proven by the construction of this graph.
     * @throws UndefinedBehaviorException If it cannot be proven that the program behavior is sufficiently defined.
     * @throws AssertionException If satisfaction of all assertions cannot be proven by the construction of this graph.
     * @throws ErrorStateException If an error state is reached.
     * @throws MemoryLeakException If the program contains a memory leak.
     */
    public void buildFullGraph(Abortion aborter)
    throws
        MemorySafetyException,
        UndefinedBehaviorException,
        AssertionException,
        ErrorStateException,
        MemoryLeakException
    {
        // no debug output
        this.buildFullGraph(false, aborter);
    }

    /**
     * Builds from the root node a full SE graph. Gives debug output if debug is true.
     * @param debug Flag for debug output.
     * @throws MemorySafetyException If memory safety of the program cannot be proven by the construction of this graph.
     * @throws UndefinedBehaviorException If it cannot be proven that the program behavior is sufficiently defined.
     * @throws AssertionException If satisfaction of all assertions cannot be proven by the construction of this graph.
     * @throws ErrorStateException If an error state is reached.
     * @throws MemoryLeakException If the program contains a memory leak.
     */
    public void buildFullGraph(boolean debug, Abortion aborter)
    throws
        MemorySafetyException,
        UndefinedBehaviorException,
        AssertionException,
        ErrorStateException,
        MemoryLeakException
    {

        int debugIndex = 1;
        while (!this.remainingGraphConstructionSteps.isEmpty()) {
            aborter.checkAbortion();

            LLVMAbstractGraphConstructionStep currentStep = popTopmostEntryFromQueue();

            executeStepAndPutSucessorStepsInQueue(currentStep, debug, aborter);


            debugIndex++;
            if (LLVMDebuggingFlags.OUTPUT_GRAPH_AFTER_EACH_NTH_STEP != 0
            		&& debugIndex % LLVMDebuggingFlags.OUTPUT_GRAPH_AFTER_EACH_NTH_STEP == 0 ) {
                this.dumpGraph();
            }
            if (LLVMDebuggingFlags.OUTPUT_DEBUG_INFO_AFTER_EACH_NTH_STEP != 0
            		&& debugIndex % LLVMDebuggingFlags.OUTPUT_DEBUG_INFO_AFTER_EACH_NTH_STEP == 0 ) {
            	LLVMCountNodesPerBasicBlock.printSortedCountPerBlock(this);
            	Date date = new Date();
                System.err.print(date);
                System.err.println("-- Nodes:" + this.getNodes().size());
            }
            if (LLVMDebuggingFlags.OUTPUT_JSON_AFTER_EACH_STEP){
                this.dumpExportGraph();
            }

            for(LLVMSEGraphEventListener listener : eventListeners) {
            	List<LLVMAbstractGraphConstructionStep> stepsAddedByEvenlistener = listener.completedGraphConstructionIterationEvent();
            	remainingGraphConstructionSteps.addAll(stepsAddedByEvenlistener);
            }
            removeObsoleteStepsFromQueue();
        }
        for(LLVMSEGraphEventListener listener : eventListeners) {
        	listener.graphFinishedEvent();
        }
        if (debug) {
            System.err.println(debugIndex);
        }
    }

    /**
     * Builds from the root node a full SE graph and gives debug output.
     * @throws MemorySafetyException If memory safety of the program cannot be proven by the construction of this graph.
     * @throws UndefinedBehaviorException If it cannot be proven that the program behavior is sufficiently defined.
     * @throws AssertionException If satisfaction of all assertions cannot be proven by the construction of this graph.
     * @throws ErrorStateException If an error state is reached and we are checking this.
     * @throws MemoryLeakException If the program contains a memory leak.
     */
    public void buildFullGraphWithDebugOutput(Abortion aborter)
    throws
        MemorySafetyException,
        UndefinedBehaviorException,
        AssertionException,
        ErrorStateException,
        MemoryLeakException
    {
        this.buildFullGraph(true, aborter);
    }

    public void dumpExportGraph() {
        final long nanos = System.nanoTime();
        final String path = System.getProperty("user.home") + "/public_html";
        File phtml = new File(path);
        if (phtml.exists()) {
            final String json = JSONExportUtil.toJSONString(this);
            final String prefix = path + "/graph" + nanos;
            try (FileWriter fw = new FileWriter(prefix + ".json")) {
                fw.write(json);
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

    /**
     * @param concreterState Some abstract state.
     * @param abstrState Some abstract state such that <code>concreterState</code> is an instance of
     *                   <code>abstrState</code>.
     * @param allocationBijection A bijective map between (subsets of) allocated areas from the more concrete state to the
     *                            more abstract state.
     * @return A mapping of references in <code>abstrState</code> to the corresponding references in
     *         <code>concreterState</code>.
     */
    public static Map<LLVMSimpleTerm, LLVMSimpleTerm> getRefCorrespondenceMap(
        LLVMAbstractState concreterState,
        LLVMAbstractState abstrState,
        Map<Integer, Integer> allocationBijection
    ) {
        Map<LLVMSimpleTerm, LLVMSimpleTerm> res = new LinkedHashMap<LLVMSimpleTerm, LLVMSimpleTerm>();
        // all used references in a generalized state must occur in the variables, the allocated areas, or
        // dereferencings thereof (other heap information is dropped during the merge)
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> vars = abstrState.getProgramVariables();
        if (vars != null) {
            for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> abstrVarEntry : vars.entrySet()) {
                LLVMSymbolicVariable concreteRef =
                    concreterState.getSymbolicVariableForProgramVariable(abstrVarEntry.getKey());
                LLVMSymbolicVariable abstrRef = abstrVarEntry.getValue().x;
                if (Globals.useAssertions) {
                    if (res.containsKey(abstrRef)) {
                        assert (res.get(abstrRef).equals(concreteRef)) : "Found contradictive mapping!";
                    }
                }
                res.put(abstrRef, concreteRef);
            }
        }
        ImmutableList<LLVMAllocation> concAllocs = concreterState.getAllocations();
        ImmutableList<LLVMAllocation> abstrAllocs = abstrState.getAllocations();
        if (concAllocs != null && abstrAllocs != null) {
            for (Map.Entry<Integer, Integer> allocMapping : allocationBijection.entrySet()) {
                LLVMAllocation concArea = concAllocs.get(allocMapping.getKey());
                LLVMAllocation abstrArea = abstrAllocs.get(allocMapping.getValue());
                if (Globals.useAssertions) {
                    if (res.containsKey(abstrArea.x)) {
                        assert (res.get(abstrArea.x).equals(concArea.x)) : "Found contradictive mapping!";
                    }
                    if (res.containsKey(abstrArea.y)) {
                        assert (res.get(abstrArea.y).equals(concArea.y)) : "Found contradictive mapping!";
                    }
                }
                res.put(abstrArea.x, concArea.x);
                res.put(abstrArea.y, concArea.y);
            }
        }
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> abstrHeap = abstrState.getMemory();
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> concHeap = concreterState.getMemory();
        if (abstrHeap != null && concHeap != null) {
            boolean changed = true;
            while (changed) {
                changed = false;
                for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> abstrHeapEntry : abstrHeap.entrySet()) {
                    LLVMMemoryRange abstrRange = abstrHeapEntry.getKey();
                    if (!res.containsKey(abstrRange.getFromRef()) || !res.containsKey(abstrRange.getToRef())) {
                        continue;
                    }
                    if (abstrHeapEntry.getValue() instanceof LLVMSimpleMemoryInvariant) {
                        LLVMSimpleTerm abstrVal =
                            ((LLVMSimpleMemoryInvariant)abstrHeapEntry.getValue()).getPointedToValue();
                        LLVMSimpleTerm res_lower = res.get(abstrRange.getFromRef());
                        LLVMSimpleTerm res_upper = res.get(abstrRange.getToRef());
                        LLVMMemoryInvariant invariant =
                            concHeap.get(new LLVMMemoryRange(res_lower, res_upper, abstrRange.getType(), abstrRange.getUnsigned()));
                        if (invariant == null) {
                            // the heap entry is implied by a struct invariant but not by a simple invariant
                            continue;
                        }
                        if (Globals.useAssertions) {
                            assert (invariant instanceof LLVMSimpleMemoryInvariant);
                        }
                        LLVMSimpleTerm concVal = ((LLVMSimpleMemoryInvariant)invariant).getPointedToValue();
                        if (abstrVal != null && concVal != null) {
                            if (res.containsKey(abstrVal)) {
                                if (Globals.useAssertions) {
                                    assert (res.get(abstrVal).equals(concVal)) : "Found contradictive mapping!";
                                }
                            } else {
                                res.put(abstrVal, concVal);
                                changed = true;
                            }
                        }
                    } else if (abstrHeapEntry.getValue() instanceof LLVMIntervalMemoryInvariant) {
                        // nothing to be done
                    } else if (abstrHeapEntry.getValue() instanceof LLVMCombinedMemoryInvariant) {
                        if (Globals.useAssertions) {
                            assert (abstrRange instanceof LLVMMemoryRecursiveRange);
                        }
                        LLVMMemoryRecursiveRange recRange = (LLVMMemoryRecursiveRange) abstrRange;
                        LLVMSimpleTerm res_lower = res.get(recRange.getFromRef());
                        LLVMSimpleTerm res_upper = res.get(recRange.getToRef());
                        LLVMSimpleTerm concLength = null;
                        for (LLVMMemoryRange concRange : concreterState.getMemory().keySet()) {
                            if (concRange instanceof LLVMMemoryRecursiveRange) {
                                if (res_lower.equals(concRange.getFromRef()) && res_upper.equals(concRange.getToRef())) {
                                    if (!res.containsKey(recRange.getLength())) {
                                        concLength = ((LLVMMemoryRecursiveRange)concRange).getLength();
                                        res.put(recRange.getLength(), concLength);
                                    }
                                }
                            }
                        }
                        for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : ((LLVMCombinedMemoryInvariant)abstrHeapEntry.getValue()).getInvariants().entrySet()) {
                            if (inv.getValue() instanceof LLVMComplexMemoryInvariant) {
                                LLVMSimpleTerm abstrFirst = ((LLVMComplexMemoryInvariant)inv.getValue()).getFirstValue();
                                LLVMSimpleTerm abstrLast = ((LLVMComplexMemoryInvariant)inv.getValue()).getLastValue();
                                LLVMMemoryInvariant concCombInv =
                                    concHeap.get(new LLVMMemoryRecursiveRange(res_lower, res_upper, recRange.getType(), concLength));
                                if (concCombInv == null) {
                                    break;
                                }
                                if (Globals.useAssertions) {
                                    assert (concCombInv instanceof LLVMCombinedMemoryInvariant);
                                }
                                LLVMMemoryInvariant concInv =
                                    ((LLVMCombinedMemoryInvariant)concCombInv).getInvariantWithOffset(inv.getKey());
                                if (Globals.useAssertions) {
                                    assert (concInv instanceof LLVMComplexMemoryInvariant);
                                }
                                LLVMSimpleTerm concFirst = ((LLVMComplexMemoryInvariant)concInv).getFirstValue();
                                LLVMSimpleTerm concLast = ((LLVMComplexMemoryInvariant)concInv).getLastValue();
                                if (abstrFirst != null && concFirst != null) {
                                    if (res.containsKey(abstrFirst)) {
                                        if (Globals.useAssertions) {
                                            assert (res.get(abstrFirst).equals(concFirst)) : "Found contradictive mapping!";
                                        }
                                    } else {
                                        res.put(abstrFirst, concFirst);
                                        changed = true;
                                    }
                                }
                                if (abstrLast != null && concLast != null) {
                                    if (res.containsKey(abstrLast)) {
                                        if (Globals.useAssertions) {
                                            assert (res.get(abstrLast).equals(concLast)) : "Found contradictive mapping!";
                                        }
                                    } else {
                                        res.put(abstrLast, concLast);
                                        changed = true;
                                    }
                                }
                            } else if (inv.getValue() instanceof LLVMSimpleMemoryInvariant) {
                                LLVMSimpleTerm abstrVal = ((LLVMSimpleMemoryInvariant)inv.getValue()).getPointedToValue();
                                LLVMMemoryInvariant concCombInv =
                                    concHeap.get(new LLVMMemoryRecursiveRange(res_lower, res_upper, recRange.getType(), recRange.getLength()));
                                if (concCombInv == null) {
                                    break;
                                }
                                if (Globals.useAssertions) {
                                    assert (concCombInv instanceof LLVMCombinedMemoryInvariant);
                                }
                                LLVMMemoryInvariant concInv =
                                    ((LLVMCombinedMemoryInvariant)concCombInv).getInvariantWithOffset(inv.getKey());
                                if (Globals.useAssertions) {
                                    assert (concInv instanceof LLVMSimpleMemoryInvariant);
                                }
                                LLVMSimpleTerm concVal = ((LLVMSimpleMemoryInvariant)concInv).getPointedToValue();
                                if (abstrVal != null && concVal != null) {
                                    if (res.containsKey(abstrVal)) {
                                        if (Globals.useAssertions) {
                                            assert (res.get(abstrVal).equals(concVal)) : "Found contradictive mapping!";
                                        }
                                    } else {
                                        res.put(abstrVal, concVal);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    } else {
                        throw new IllegalStateException("unknown invariant type");
                    }
                }
            }
        }
        return res;
    }

    /**
     * Creates an SVG file to view the graph (for debugging purposes).
     */
    public void dumpGraph() {
    	dumpGraph(LLVMDebuggingFlags.COMPACT_GRAPH_BEFORE_OUTPUT);
    }

    public void dumpGraph(boolean compactBeforeDump) {
    	if(compactBeforeDump) {
    		LLVMSEGraphOutputCompactor.compactGraphForOutput(this).dumpGraph(false);
    	} else {
			final long nanos = System.nanoTime();
			final String path = System.getProperty("user.home") + "/public_html";
			File phtml = new File(path);
			if (phtml.exists()) {
				final String dotString = this.toDOT();
				// String latest = "latest" + ".svg";
				final String prefix = path + "/graph" + nanos;
				try (FileWriter fw = new FileWriter(prefix + ".dot")) {
					fw.write(dotString);
				} catch (IOException e) {
					e.printStackTrace();
				}
				try {
					// Runtime.getRuntime().exec("rm " + path + "/latest.dot");
					Runtime.getRuntime().exec("dot " + prefix + ".dot  -Tpdf -o " + prefix + ".pdf").waitFor();
					// Path target = new File(prefix + ".dot").toPath();
					// Path newLink = new File(path +"/latest.dot").toPath();
					// new File(path +"/latest.dot").delete();
					// Files.createSymbolicLink(newLink, target);
					// Files.createLink(newLink, target);
				} catch (IOException e) {
					e.printStackTrace();
				} catch (UnsupportedOperationException x) {
					// Some file systems do not support symbolic links.
					System.err.println(x);
				}
				// catch(InterruptedException e) { } //only needed when
				// Runtime.getRuntime.exec is used
				catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
    	}
    }

    @Override
    public boolean equals(Object o) {
        // up to now, we never encountered a case where we needed to compare whole graphs
        return super.equals(o);
    }

    /**
     * @return A map which gives to every basic block a list of nodes whose instruction is the first within the
     *         corresponding block.
     */
    public Map<ImmutablePair<String, String>, List<Node<LLVMAbstractState>>> getBlockToNode() {
        return this.blockToNode;
    }



    /**
     * @return A string with the number of edges of each type:
     */
    public String getEdgeInformation() {
        // determine the number of edges
        int numberOfEvalEdges = 0;
        int numberOfGeneralizeEdges = 0;
        int numberOfInstanceEdges = 0;
        int numberOfRefineEdges = 0;
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : this.getEdges()) {
            if (edge.getObject() instanceof LLVMEvaluationInformation) {
                numberOfEvalEdges++;
            } else if (edge.getObject() instanceof LLVMGeneralizationInformation) {
                numberOfGeneralizeEdges++;
            } else if (edge.getObject() instanceof LLVMInstantiationInformation) {
                numberOfInstanceEdges++;
            } else if (edge.getObject() instanceof LLVMRefinementInformation) {
                numberOfRefineEdges++;
            }
        }
        // create string
        StringBuilder res = new StringBuilder();
        res.append("(eval: ");
        res.append(numberOfEvalEdges);
        res.append(", refine: ");
        res.append(numberOfRefineEdges);
        res.append(", instance: ");
        res.append(numberOfInstanceEdges);
        res.append(", generalize: ");
        res.append(numberOfGeneralizeEdges);
        res.append(")");
        return res.toString();
    }

    /**
     * Follow the outward edges of a node until evaluation edges are reached.
     * @param startNode The node whose successors are desired
     * @return A set containing the node directly after the first evaluation edge
     *         for each path going out of the startNode
     */
    public Set<Node<LLVMAbstractState>> getEvalSuccessors(Node<LLVMAbstractState> startNode) {
        Set<Node<LLVMAbstractState>> result = new LinkedHashSet<>();
        Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> nextEdges = this.getOutEdges(startNode);
        while (!nextEdges.isEmpty()) {
            Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> currentEdges = nextEdges;
            nextEdges = new LinkedHashSet<>();
            for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : currentEdges) {
                Node<LLVMAbstractState> target = edge.getEndNode();
                if (edge.getObject() instanceof LLVMEvaluationInformation) {
                    result.add(target);
                } else {
                    nextEdges.addAll(this.getOutEdges(target));
                }
            }
        }
        return result;
    }

    /**
     * Like SimpleGraph.getSCCs(), but return a set of LLVMSELoop instances
     * @author Hermann Walth
     * @return The set of loops occurring in this graph
     * @see aprove.verification.oldframework.Utility.Graph.SimpleGraph#getSCCs()
     */
    public Set<LLVMSELoop> getLoops() {
        Set<Cycle<LLVMAbstractState>> cycles = this.getSCCs();
        LinkedHashSet<LLVMSELoop> loops = new LinkedHashSet<LLVMSELoop>();
        for (Cycle<LLVMAbstractState> cycle : cycles) {
            loops.add(new LLVMSELoop(cycle, this));
        }
        return loops;
    }

    /**
     * @return The module we're analyzing with this graph
     */
    public LLVMModule getModule() {
        return this.module;
    }

    /**
     * @return This graph's root node
     */
    public Node<LLVMAbstractState> getRoot() {
        return this.root;
    }

    /**
     * @return The strategy parameters.
     */
    public LLVMParameters getStrategyParameters() {
        return this.strategyParameters;
    }

    public boolean isNodeUnneeded(Node<LLVMAbstractState> node) {
    	return !contains(node) || unneededNodes.contains(node);
    }

    @Override
    public int hashCode() {
        // up to now, we never encountered a case where we needed to compare whole graphs
        return super.hashCode();
    }

    public boolean hasPathNotSteppingOverUnneededNodes(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end) {
    	// this method is copied from SimpleGraph::hasPath, but does not follow edges over unneeded nodes
        // TODO avoid code duplication
        if (Globals.useAssertions) {
            assert (start != null && end != null);
        }
        Set<Node<LLVMAbstractState>> done = new HashSet<Node<LLVMAbstractState>>();
        done.add(start);
        Stack<Node<LLVMAbstractState>> todo = new Stack<Node<LLVMAbstractState>>();
        todo.push(start);
        while (!todo.isEmpty()) {
            Node<LLVMAbstractState> node = todo.pop();
            if (node.equals(end)) {
                return true;
            }
            if (this.unneededNodes.contains(node)) {
                continue;
            }
            for (Node<LLVMAbstractState> succ : this.getOut(node)) {
                if (done.add(succ)) {
                    todo.push(succ);
                }
            }
        }
        return false;
    }

    @Override
    public String toDOT() {
        return this.toDOT(true, LLVMDebuggingFlags.USE_HTML_DOT_LAYOUT);
    }

    @Override
    public String toDOT(boolean showNrs) {
        return this.toDOT(showNrs, LLVMDebuggingFlags.USE_HTML_DOT_LAYOUT);
    }

	/**
	 * @param showNrs
	 *            TODO
	 * @see aprove.verification.oldframework.Utility.Graph.SimpleGraph#toDOT(boolean)
	 * @param useHTMLLayout
	 *            specifies whether or not the tabular HTML layout should be
	 *            used
	 * @return TODO
	 */
	public String toDOT(boolean showNrs, boolean useHTMLLayout) {
		// Transforms this TerminationGraph into <em>one</em> dotty file
		// containing
		// one cluster for every methodgraph.
		StringBuilder t = new StringBuilder();
		t.append("digraph dp_graph {\n");
		t.append("graph [mindist=0.3,nodesep=0.20,concentrate=true,ranksep=0.5];\n");
		// The new tabular layout requires "plaintext" shapes to avoid doubled
		// frames.
		if (useHTMLLayout) {
			t.append("node [shape=plaintext,fontsize=10];\n");
		} else {
			t.append("node [shape=rectangle,fontsize=10];\n");
		}
		t.append("edge [labeldistance=3,headclip=true,fontsize=8];\n");
		Iterator<Node<LLVMAbstractState>> i = getNodes().iterator();
		while (i.hasNext()) {
			Node<LLVMAbstractState> from = i.next();
			if (!this.contains(from)) {
				continue;
			}
			t.append(from.getNodeNumber());
			t.append(" [");
			if (from.getObject() != null) {
				if (useHTMLLayout) {
					t.append("label=<\n");
					/*
					 * We are only interested in the predecessor if it's unique
					 * and connected with an Evaluation or Refinement Edge.
					 */
					Set<Node<LLVMAbstractState>> set = this.getIn(from);
					assert set != null;
					@SuppressWarnings("unchecked")
					Node<LLVMAbstractState> predecessorNode = this.getIn(from).size() == 1
							? ((Node<LLVMAbstractState>) this.getIn(from).toArray()[0]) : null;
					LLVMAbstractState predecessorState = null;
					if (predecessorNode != null
							&& (this.getEdgeObject(predecessorNode, from) instanceof LLVMEvaluationInformation
									|| this.getEdgeObject(predecessorNode, from) instanceof LLVMRefinementInformation
									|| this.getEdgeObject(predecessorNode, from) instanceof LLVMMethodSkipEdge)) {
						predecessorState = predecessorNode.getObject();
					}
					final int nodeNumer = showNrs ? from.getNodeNumber() : -1;
					Boolean isUniqueFunctionStart = null;
					t.append(from.getObject().toDOTString(true, nodeNumer, predecessorState,
							null /* Fix for missing function graph */, this.unneededNodes.contains(from),
							isUniqueFunctionStart));
					t.append(">, ");
				} else {
					t.append("label=\"");
					t.append((showNrs ? from.getNodeNumber() + ": " : ""));
					t.append(this.getDOTNodeLabelText(SimpleGraph.DOT, from));
					t.append("\", ");
				}
			}
			t.append(this.getDOTFormatForNodeLabels(SimpleGraph.DOT, from));
			t.append("];\n");
		}

		Iterator<Edge<LLVMEdgeInformation, LLVMAbstractState>> it = this.getEdges().iterator();
		while (it.hasNext()) {
			Edge<LLVMEdgeInformation, LLVMAbstractState> edge = it.next();
			LLVMEdgeInformation edgeInfo = edge.getObject();
			Node<LLVMAbstractState> from = edge.getStartNode();
			Node<LLVMAbstractState> to = edge.getEndNode();
			t.append(from.getNodeNumber());
			t.append(" -> ");
			t.append(to.getNodeNumber());
			t.append(" [color=");
			t.append(edgeInfo.getDotColor());
			t.append(", label=\"");
			t.append(edgeInfo.getDotLabel());
			t.append("\"];\n");
		}
		t.append("}\n");
		return t.toString();
	}

    @Override
    public JSONObject toJSON(){
		JSONObject res = new JSONObject();
		res.put("type", "Graph");
		JSONObject jsonNodes = new JSONObject();
		jsonNodes.put("type", "Nodes");
		for (Node<LLVMAbstractState> from : getNodes()) {
			jsonNodes.put("" + from.getNodeNumber(), JSONExportUtil.toJSON(from.getObject()));
		}

		res.put("nodes", jsonNodes);
		res.put("edges", JSONExportUtil.toJSON(this.getEdges()));
		return res;
    }

    @Override
    protected String getDOTFormatForNodeLabels(int method, Node<LLVMAbstractState> node) {
        LLVMAbstractState state = node.getObject();
        String color;
        if (state.isErrorState()) {
            color = "color=red, style=filled, fillcolor=orangered, ";
        } if (state.isInconsistentState()) {
                color = "color=yellow, style=filled, fillcolor=lightyellow, ";
        } else if (state.isEnd()) {
            color = "color=green, style=filled, fillcolor=lawngreen, ";
        } else if (this.root.equals(node)) {
            color = "color=blue, style=filled, fillcolor=lightblue, ";
        } else if(isNodeUnneeded(node)) {
        	color = "color=gray, style=filled, fillcolor=lightgray, ";
        } else{
            color = "";
        }
        switch (method) {
            case DOT:
            case DOTDOT2:
            case SAVE:
            case EDGES:
            case DOTDOT1:
                return color + "fontsize=16";
            case INTERACTIVE:
                return color + "fontsize=10";
            default:
                return "";
        }
    }

    /**
     * @param generalizedNode some old node which was now generalized to something else
     * @return all nodes only reachable from the generalizedNode (i.e., if we want to ignore that one, we can
     *  ignore these successors too)
     */
    @Deprecated
    public Collection<Node<LLVMAbstractState>> findUnneededNodes(Node<LLVMAbstractState> generalizedNode, Abortion aborter) {
        return findUnneededNodes(Collections.singleton(generalizedNode), Collections.emptySet(), null, aborter);
    }

    public Set<Node<LLVMAbstractState>> findUnneededNodes(
        Set<Node<LLVMAbstractState>> initial,
        Set<Node<LLVMAbstractState>> dontFollow,
        //Set<Class<? extends LLVMEdgeInformation>> ignoreEdgeTypes,
        EdgeFilter<LLVMEdgeInformation, LLVMAbstractState> edgeFilter,
        Abortion aborter
    ) {
        Set<Node<LLVMAbstractState>> newUnneededNodes = new LinkedHashSet<Node<LLVMAbstractState>>();
        newUnneededNodes.addAll(initial);
        newUnneededNodes.removeAll(dontFollow);
        LinkedList<Node<LLVMAbstractState>> toCheck = new LinkedList<Node<LLVMAbstractState>>();
        for (Node<LLVMAbstractState> node : initial) {
            if (dontFollow.contains(node)) {
                continue;
            }

            toCheck.addAll(getOut(node));

        }

        while (!toCheck.isEmpty()) {
        	aborter.checkAbortion();
            Node<LLVMAbstractState> nodeToCheck = toCheck.pop();


            if (dontFollow.contains(nodeToCheck)) {
                continue;
            }

            boolean needed = false;
            outer:
            for (Edge<LLVMEdgeInformation,LLVMAbstractState> e : getInEdges(nodeToCheck)) {
                if (newUnneededNodes.contains(e.getStartNode())) {
                    continue;
                }

                //if we get here, the node is needed:
                needed = true;

            }

            if (!needed) {
                if (newUnneededNodes.add(nodeToCheck)) {
                	for(Edge<LLVMEdgeInformation,LLVMAbstractState> outEdge : getOutEdges(nodeToCheck))
                		if(edgeFilter == null || edgeFilter.selectEdge(outEdge.getStartNode(), outEdge.getEndNode(), outEdge.getObject())) {
                			toCheck.add(outEdge.getEndNode());
                		}

                }
            }
        }
        return newUnneededNodes;
    }

    /**
     * Marking a node as unneeded means that it is only kept in the graph for debugging purposes.
     * This will not remove the node, but remove it from some internal structures and notify listeners
     */
	public void markNodeUnneeded(Node<LLVMAbstractState> node) {
		if(Globals.useAssertions) {
			assert contains(node) : "GRAPH CONSISTENCY ERROR: Trying to mark node as unneeded that is not in graph";
		}
		boolean alreadyUnneeded = !unneededNodes.add(node);
		if (!alreadyUnneeded) {
			handleNodeRemovalOrUnneeded(node, false);

			Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> unneededEdges = new LinkedHashSet<>();

			for(Edge<LLVMEdgeInformation, LLVMAbstractState> inEdge : getInEdges(node)) {
				Node<LLVMAbstractState> otherNode = inEdge.getStartNode();
				if(otherNode != node && !isNodeUnneeded(otherNode)) {
					unneededEdges.add(inEdge);
				}
			}
			for(Edge<LLVMEdgeInformation, LLVMAbstractState> outEdge : getOutEdges(node)) {
				Node<LLVMAbstractState> otherNode = outEdge.getEndNode();
				if(otherNode != node && !isNodeUnneeded(otherNode)) {
					unneededEdges.add(outEdge);
				}
			}

			for(Edge<LLVMEdgeInformation, LLVMAbstractState> unneededEdge : unneededEdges) {
				handleEdgeRemovalOrUnneeded(unneededEdge.getStartNode(), unneededEdge.getEndNode(), unneededEdge.getObject(), false);
			}
		}
	}

    private void removeNodeFromInternalStructures(Node<LLVMAbstractState> node, boolean removeFromUnneededNodes) {
    	LLVMProgramPosition nPos = node.getObject().getProgramPosition();
        ImmutablePair<String, String> nBlock = new ImmutablePair<String, String>(nPos.x, nPos.y);
        if (blockToNode.containsKey(nBlock)) {
        	blockToNode.get(nBlock).remove(node);
        }

        if(removeFromUnneededNodes)
        	unneededNodes.remove(node);

    }

    private void handleNodeRemovalOrUnneeded(Node<LLVMAbstractState> node, boolean removed) {
    	if(Globals.useAssertions) {
    		assert root != node;
    	}
    	removeNodeFromInternalStructures(node, removed);
    	for (LLVMSEGraphEventListener listener : eventListeners) {
			List<LLVMAbstractGraphConstructionStep> stepsAddedByEvenlistener = listener.nodeRemovedOrUnneeded(node, currentlyActiveStep, removed);
			currentlyActiveStep.addStepsCreatedByGraphListenersWhilePerforming(stepsAddedByEvenlistener);
		}
    }

    private void handleEdgeRemovalOrUnneeded(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end, LLVMEdgeInformation label, boolean removed) {
    	for (LLVMSEGraphEventListener listener : eventListeners) {
			List<LLVMAbstractGraphConstructionStep> stepsAddedByEvenlistener = listener.edgeRemovedOrUnneeded(start, end, label, currentlyActiveStep, removed);
			currentlyActiveStep.addStepsCreatedByGraphListenersWhilePerforming(stepsAddedByEvenlistener);
		}
    }

    private void handleNodeAddition(Node<LLVMAbstractState> node) {
    	for (LLVMSEGraphEventListener listener : eventListeners) {
			List<LLVMAbstractGraphConstructionStep> stepsAddedByEvenlistener = listener.nodeAddedEvent(node, currentlyActiveStep);
			currentlyActiveStep.addStepsCreatedByGraphListenersWhilePerforming(stepsAddedByEvenlistener);
		}
    }

    private void handleEdgeAddition(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end, LLVMEdgeInformation label) {
    	for (LLVMSEGraphEventListener listener : eventListeners) {
			List<LLVMAbstractGraphConstructionStep> stepsAddedByEvenlistener = listener.edgeAddedEvent(start, end, label, currentlyActiveStep);
			currentlyActiveStep.addStepsCreatedByGraphListenersWhilePerforming(stepsAddedByEvenlistener);
		}
    }

	@Override
	public boolean removeNode(Node<LLVMAbstractState> node) {
		Set<Edge<LLVMEdgeInformation, LLVMAbstractState >> involvedEdges = new LinkedHashSet<>(getInEdges(node));
		involvedEdges.addAll(getOutEdges(node));

		boolean contained = super.removeNode(node);

		if (contained) {
			for(Edge<LLVMEdgeInformation, LLVMAbstractState> edge : involvedEdges ) {
				handleEdgeRemovalOrUnneeded(edge.getStartNode(), edge.getEndNode(), edge.getObject(), true);
			}
			handleNodeRemovalOrUnneeded(node, true);
		}
		return contained;
	}

	@Override
	public boolean addNode(Node<LLVMAbstractState> node) {
		boolean wasAdded = super.addNode(node);
		if (wasAdded) {
			handleNodeAddition(node);
		}
		return wasAdded;
	}

	@Override
	public boolean addEdge(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end, LLVMEdgeInformation label) {
		//Call to addNode in superclass version, which involves calling addNode
    	boolean wasAdded = super.addEdge(start,end,label);
    	if(wasAdded) {
    		handleEdgeAddition(start, end, label);
    	}
    	return wasAdded;
	}

    @Override
    public LLVMEdgeInformation removeEdgeAndReturnLabel(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end) {
    	LLVMEdgeInformation label = super.removeEdgeAndReturnLabel(start, end);
    	handleEdgeRemovalOrUnneeded(start, end, label, true);
    	return label;
    }

    @Override
    public void clearGraph() {
    	//Not yet implemented
    	throw new UnsupportedOperationException();
    }

    @Override
    public LLVMEdgeInformation replaceEdge(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end,
    		LLVMEdgeInformation label) {
    	//Not yet implemented
    	throw new UnsupportedOperationException();
    }

    @Override
    public boolean addEdge(Edge<LLVMEdgeInformation, LLVMAbstractState> edge) {
    	return this.addEdge(edge.getStartNode(), edge.getEndNode(), edge.getObject());
    }

    @Override
    public boolean addEdge(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end) {
    	return this.addEdge(start, end, null);
    }

    @Override
    public void removeEdge(Edge<LLVMEdgeInformation, LLVMAbstractState> edge) {
    	this.removeEdgeAndReturnLabel(edge.getStartNode(), edge.getEndNode());
    }

    @Override
    public void removeEdge(Node<LLVMAbstractState> start, Node<LLVMAbstractState> end) {
    	this.removeEdgeAndReturnLabel(start, end);
    }

    public final void addSEGraphEventListener(LLVMSEGraphEventListener listener) {
    	eventListeners.add(listener);
    }

    public void removeSEGraphEventListener(LLVMSEGraphEventListener listener) {
    	eventListeners.remove(listener);
    }

    public void setRoot(Node<LLVMAbstractState> root) {
    	if(this.root != null) {
    		throw new IllegalStateException("Must not change root");
    	}
    	this.root = root;
    }

    /*
     * functionName without scope (i.e. @)
     */
    @Deprecated /* Done by LLVMIntersectionHeuristics now */
    public void flagFunctionAsRecursive(String functionName) {
    	recursiveFunctions.add(functionName);
    }

    /*
     * functionName without scope (i.e. @)
     */
    @Deprecated /* Stop using this, this is now done by the intersection heuristics */
    public boolean isRecursiveFunction(String functionName) {
    	return recursiveFunctions.contains(functionName);
    }

    @Deprecated /* Done by LLVMIntersectionHeuristics now */
    public Set<String> getRecursiveFunctions() {
    	return recursiveFunctions;
    }

    public LLVMIntersectionHeuristics getIntersectionHeuristics() {
    	return intersectionHeuristics;
    }


    private void executeStepAndPutSucessorStepsInQueue(LLVMAbstractGraphConstructionStep stepToExecute, boolean debug, Abortion aborter) throws MemorySafetyException, UndefinedBehaviorException, AssertionException, ErrorStateException, MemoryLeakException {
    	this.currentlyActiveStep = stepToExecute;
    	List<LLVMAbstractGraphConstructionStep> newSteps = stepToExecute.perform(aborter, debug);

    	/*
    	 * To make life easier, we first put ALL the steps in the queue that were created during performing the step above.
    	 * Only after then we put all the steps in the queue that were created by event listeners.
    	 */

    	this.currentlyActiveStep = null;

        putElementsInQueue(newSteps);

        putElementsInQueue(stepToExecute.getStepsEvokedByGrahpListenersWhilePerformingStep());


    }

    private void removeObsoleteStepsFromQueue() {
    	Iterator<LLVMAbstractGraphConstructionStep> stepIterator = remainingGraphConstructionSteps.iterator();
    	while(stepIterator.hasNext()) {
    		if(stepIterator.next().isObsolete()) {
    			stepIterator.remove();
    		}
    	}
    }

    public boolean anyGraphConstructionStepInQueueMatchesPredicate(Predicate<LLVMAbstractGraphConstructionStep> p) {
    	return remainingGraphConstructionSteps.stream().anyMatch(p);
    }

    private LLVMAbstractGraphConstructionStep popTopmostEntryFromQueue() {
    	if(remainingGraphConstructionSteps.isEmpty())
    		return null;
    	Iterator<LLVMAbstractGraphConstructionStep> it = remainingGraphConstructionSteps.iterator();
    	LLVMAbstractGraphConstructionStep step = it.next();
    	it.remove();
    	return step;
    }

    private void putElementsInQueue(List<LLVMAbstractGraphConstructionStep> newQueueEntries) {
    	if(Globals.useAssertions) {
    		assert currentlyActiveStep == null: "Only change the queue after executing a step, not while executing it";
    	}

    	remainingGraphConstructionSteps.addAll(newQueueEntries);
    }

    public LLVMFunctionGraphTracker getFunctionGraphTracker() {
        return functionGraphTracker;
    }

    public LLVMForceMergeHeuristic getForceMergeHeurisics() {
    	return forceMergeHeuristics;
    }

    private void initIntersectionStructures(LLVMParameters parameters, LLVMModule module,Abortion aborter) {
        this.intersectionHeuristics = new LLVMIntersectionHeuristics(module,parameters,aborter);
        this.functionGraphTracker = new LLVMFunctionGraphTracker(this,this.intersectionHeuristics);

        addSEGraphEventListener(this.functionGraphTracker);

        addSEGraphEventListener(new LLVMEntryNodeOfRecursiveFunctionRemovedOrUnneededListener(this));
        addSEGraphEventListener(new LLVMNewIntersectionNeededListener(this));
        addSEGraphEventListener(new LLVMReturnNodeRemovedOrUnneededListener(this));
    }


	public LLVMLiveVariableAnalysis getLiveVariableAnalysis() {
		return liveVariableAnalysis;
	}

}
