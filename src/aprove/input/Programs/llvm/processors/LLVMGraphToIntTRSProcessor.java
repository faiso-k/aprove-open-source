package aprove.input.Programs.llvm.processors;

import aprove.Globals;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

import java.util.*;
import java.util.logging.Level;
import java.util.logging.Logger;

import static aprove.verification.dpframework.IDPProblem.IGeneralizedRule.*;
import static aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.TerminationSCCToIDPv1Processor.*;
import static aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.*;

/**
 * This processor takes a symbolic execution graph SCC and translates it to an intTRS problem by converting each edge
 * of the SCC to an intTRS rewrite rule and simplifying these.
 * @author Marc Brockschmidt, cryingshadow
 */
public abstract class LLVMGraphToIntTRSProcessor extends LLVMGraphProcessor {

    /**
     * The logger we keep for logging our logs.
     */
    private static Logger log = Logger.getLogger("aprove.verification.oldframework.LLVM.Processors.LLVMTerminationSCCToIRSProcessor");

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LLVMGraphToIntTRSProcessor(Arguments arguments) {
        super(arguments);
    }

    /**
     * Work on the given obligation.
     * @param obl a TerminationGraphProblem
     * @param oblNode ignored.
     * @param aborter some aborter
     * @param rti ignored.
     * @param implication The implication that should be used to connect the IntTRS problems to this problem.
     * @return one obligation per SCC
     */
    protected Result process(
        BasicObligation obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti,
        Implication implication
    ) {
        List<Pair<String, ? extends RuleSet>> conversionLog = new LinkedList<Pair<String, ? extends RuleSet>>();
        Node<LLVMAbstractState> startNode = getStartNode(obl);
        
        if (Globals.useAssertions) {
            if (startNode != null) {
                assert getNodes(obl).contains(startNode);
                boolean outgoingEdgeFromStartNode = false;
                for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : getEdges(obl)) {
                    if (edge.getStartNode().equals(startNode)) {
                        outgoingEdgeFromStartNode = true;
                        break;
                    }
                }
                assert outgoingEdgeFromStartNode;
            }
        }
        
        boolean needOverapproximation;
        if (implication == YNMImplication.SOUND) {
            needOverapproximation = true;
        } else {
            needOverapproximation = false;
        }
        
        if (!this.useOverapproximation && needOverapproximation) {
            return ResultFactory.unsuccessful("the parameter to this processor does not allow overapproximation, but it is required for the conversion.");
        }
        
        IRSProblem problem = this.transformGraphToIRS(getNodes(obl), getEdges(obl), startNode, conversionLog, needOverapproximation, aborter);
        problem.setParent(obl);
        problem.setOverapproximates(needOverapproximation);
        
        if (Globals.useAssertions) {
            if (problem.getStartTerm() != null) {
                assertSetContainsRuleForFunctionSymbol(problem.getRules(), problem.getStartTerm().getFunctionSymbol());
            }
        }
        
        return ResultFactory.proved(problem, implication, createProof(conversionLog));
    }
    
    public abstract Set<Node<LLVMAbstractState>> getNodes(BasicObligation problem);
    
    public abstract Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> getEdges(BasicObligation problem);
    
    /**
     * Return the start node for the IntTRS. May return null if the IntTRS should be evaluated without a start state
     */
    public abstract Node<LLVMAbstractState> getStartNode(BasicObligation problem);
    
    public abstract Proof createProof(List<Pair<String, ? extends RuleSet>> conversionLog);
    
    /**
     * Work on the given obligation.
     * @param nodes The nodes in the graph to transform to the IRS
     * @param edges The edges in the graph to transform to the IRS
     * @param startNode The start node for the IRS. May return null if the IRS should be evaluated without a start node
     * @param conversionLog A list which we use to document all translation steps we performed.
     * @param allowOverapproximation Whether transformations that destroy the completeness of the proof may be performed  
     * @param aborter The aborter that may tell us to stop.
     * @return An IRSProblem corresponding to the transformed SCC, where termination of the IRS implies termination of
     *         the SCC.
     */
    public IRSProblem transformGraphToIRS(
        Set<Node<LLVMAbstractState>> nodes,
        Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> edges,
        Node<LLVMAbstractState> startNode,
        List<Pair<String, ? extends RuleSet>> conversionLog,
        boolean allowOverapproximation,
        Abortion aborter
    ) {
        final Pair<Set<IGeneralizedRule>, Map<Node<LLVMAbstractState>, TRSFunctionApplication>> ruleSetNodeMap = this.translateGraphToRuleSet(nodes, edges, conversionLog, aborter);
        Set<IGeneralizedRule> rules = ruleSetNodeMap.x;
        Map<Node<LLVMAbstractState>, TRSFunctionApplication> nodeMap = ruleSetNodeMap.y;
        FunctionSymbol startSymbol = null;
        if (startNode != null) {
            startSymbol = nodeMap.get(startNode).getFunctionSymbol();
        }

        //Simplify the prepared rules, only if combineRules is allowed:
        Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> combinedRulesMap = new HashMap<>();
        Set<IGeneralizedRule> iGRules;
        if (this.combineRules) {
        iGRules = this.simplifyRuleSet(
                rules,
                conversionLog,
                aborter,
                allowOverapproximation,
                /*filterFreeVarsFromCond=*/false,
                startSymbol,
                combinedRulesMap
            );
        }
        else {
            iGRules = new HashSet<>(rules);
        }
        
        assertSetContainsRuleForFunctionSymbol(iGRules, startSymbol);
        
        Map<FunctionSymbol, Node<LLVMAbstractState>> functionSymbolToAbstractState = new HashMap<>();
        for (Node<LLVMAbstractState> state : nodeMap.keySet()) {
            functionSymbolToAbstractState.put(nodeMap.get(state).getFunctionSymbol(), state);
        }
        
        IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        //Transform into the (syntactically restricted) intTRS format:
        LinkedHashSet<IGeneralizedRule> newRules = new LinkedHashSet<>();
        for (IGeneralizedRule rule : iGRules) {
            IGeneralizedRule newRule = IRSwTFormatTransformer.moveArithmeticToConstrains(rule, predefinedMap);
            //Remove ! (does not exist anyway, done) and != and the ensuing ||:
            boolean dontRemove = rule.getLeft().getFunctionSymbol().equals(startSymbol);
            Set<IGeneralizedRule> tmp =
                IRSwTFormatTransformer.removeDivModAndNotAndNotEqualAndOrAndFalse(newRule, RoundingBehaviour.TOWARDS_ZERO, predefinedMap, dontRemove, true);
            newRules.addAll(tmp);
            // if new rules added with new function symbol, add the state of the original fs also to this new fs 
            for (IGeneralizedRule cur : tmp) {
                FunctionSymbol fs = cur.getLeft().getFunctionSymbol();
                if (!functionSymbolToAbstractState.containsKey(fs)) {
                    //functionSymbolToAbstractState.put(fs, functionSymbolToAbstractState.get(rule.getLeft().getFunctionSymbol()));
                }
            }
        }
        iGRules = newRules;
        
        Set<FunctionSymbol> dontRemove = startSymbol == null ? Collections.emptySet() : Collections.singleton(startSymbol);
        assertSetContainsRuleForFunctionSymbol(iGRules, startSymbol);
        iGRules = cleanConstraints(iGRules, dontRemove, false, true, predefinedMap, aborter);
        assertSetContainsRuleForFunctionSymbol(iGRules, startSymbol);
        iGRules = removeTrivialConstraints(iGRules, predefinedMap);
        assertSetContainsRuleForFunctionSymbol(iGRules, startSymbol);
        iGRules = removePredefinedOpsOnLhs(iGRules, predefinedMap);
        assertSetContainsRuleForFunctionSymbol(iGRules, startSymbol);
        iGRules = makeLhsLinear(iGRules, predefinedMap);
        assertSetContainsRuleForFunctionSymbol(iGRules, startSymbol);
        conversionLog.add(
            new Pair<String, RuleSet>(
                "Removed division, modulo operations, cleaned up constraints. Obtained " + iGRules.size() + " rules.",
                new IGeneralizedRuleSet(iGRules, null)
            )
        );
        
        final TRSFunctionApplication startTerm;
        if (startNode != null) {
            assert !Globals.useAssertions || nodeMap.get(startNode) != null;
            startTerm = nodeMap.get(startNode);
        } else {
            startTerm = null;
        }

        // infer variable renaming before creating the problem
        CollectionMap<String, String> variableRenaming = new CollectionMap<>();
        iGRules.forEach(rule -> {
            rule.getVariables().stream().map(TRSVariable::getName)
                .filter(varName -> varName.contains(":"))
                .forEach(varName ->
                    variableRenaming.add(varName.substring(0, varName.lastIndexOf(":")), varName));
        });

        IRSProblem problem = new IRSProblem(ImmutableCreator.create(iGRules), startTerm);
        problem.setVariableRenaming(variableRenaming);
        problem.setFunctionSymbolAbstractStateMap(functionSymbolToAbstractState);
        problem.setCombinedRulesMap(combinedRulesMap);

        for (Pair<String, ? extends RuleSet> msg : conversionLog) {
            LLVMGraphToIntTRSProcessor.log.log(Level.FINE, msg.x);
            for (Rule rule : msg.y) {
                LLVMGraphToIntTRSProcessor.log.log(Level.FINE, rule.toString());
            }
        }

        return problem;
    }
}
