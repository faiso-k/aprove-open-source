package aprove.input.Programs.llvm.processors;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.JBCPreprocessing.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.Compression.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

import java.util.*;
import java.util.logging.Level;

/**
 * This processor takes an SCC of a symbolic execution graph and translates it to a rewrite system problem by
 * converting each edge of the SCC to a rewrite rule and simplifying these.
 * @author CorneliusAschermann, Christian von Essen, Matthias Hoelzel, Marc Brockschmidt, cryingshadow
 */
public abstract class LLVMGraphProcessor extends Processor.ProcessorSkeleton {

    /**
     * If set, we encode all knowledge on instance edges into the rules.
     */
    private final LLVMInvariants useInvariants;
    
    
    /**
     * If set, rules on linear paths are combined to one single rule (this is the default)
     * If not set, this combining step is skipped
     * Not combining is needed for the witness generation for LoAT as the backend
     */
    protected final boolean combineRules;
    
    /**
     * If set, over-approximation are allowed. 
     * Otherwise an over-approximation leads to aborting this processor.
     * Can be used for backends that use under-approximation and 
     * thus are invalid when there was an over-approximations beforehand.
     * This is just used to reduce unnecessary computation.
     */
    protected final boolean useOverapproximation;

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public LLVMGraphProcessor(LLVMGraphProcessor.Arguments arguments) {
        this.useInvariants = arguments.useInvariants;
        this.combineRules = arguments.combineRules;
        this.useOverapproximation = arguments.useOverapproximation;
    }

    /**
     * @return The rule created from the edge.
     * @param actEdge Can currently be InstatiationInformation, RefinementInformation, or EvaluationInformation.
     * @param nodeMap Used to find the function applications corresponding to the start/end node.
     */
    public IGeneralizedRule inferRuleFromEdge(
        Edge<LLVMEdgeInformation, LLVMAbstractState> actEdge,
        LinkedHashMap<Node<LLVMAbstractState>, TRSFunctionApplication> nodeMap
    ) {
        Node<LLVMAbstractState> startNode = actEdge.getStartNode();
        Node<LLVMAbstractState> endNode = actEdge.getEndNode();
        LLVMEdgeInformation actLabel = actEdge.getObject();
        TRSFunctionApplication startNodeTerm = nodeMap.get(startNode);
        TRSFunctionApplication endNodeTerm = nodeMap.get(endNode);
        TRSTerm conditionTerm =
            this.useInvariants.getCondition(startNode.getObject(), endNode.getObject(), actLabel);
        if (actLabel instanceof LLVMInstantiationInformation) {
            Substitution sigma = ((LLVMInstantiationInformation)actLabel).toSubstitution();
            endNodeTerm = endNodeTerm.applySubstitution(sigma);
            conditionTerm = conditionTerm.applySubstitution(sigma);
        }
        if (actLabel instanceof LLVMContextConcretizationEdge) {
            // we currently don't want them in the TRS
            return null;
        }
        if (Globals.useAssertions) {
            assert (startNodeTerm != null && endNodeTerm != null) : "There should be a non empty term for each state.";
        }
        return IGeneralizedRule.create(startNodeTerm, endNodeTerm, conditionTerm);
    }
    
    public Set<IGeneralizedRule> simplifyRuleSet(
                                                 Set<IGeneralizedRule> rules,
                                                 List<Pair<String, ? extends RuleSet>> conversionLog,
                                                 Abortion aborter,
                                                 boolean allowOverapproximation,
                                                 boolean filterFreeVarsFromCond,
                                                 FunctionSymbol startSymbol
                                             ) {
        return this.simplifyRuleSet(rules, conversionLog, aborter, allowOverapproximation, filterFreeVarsFromCond, startSymbol, null);
    }

    /**
     * @param rules A set of rules obtained for an SCC of a symbolic execution graph.
     * @param conversionLog A log of things we have done to obtain the resulting set of rules.
     * @param aborter The aborter that may tell us to stop.
     * @param filterFreeVarsFromCond Shall we filter free variables from conditions?
     * @param allowOverapproximation Whether transformations that destroy the completeness of the proof may be performed
     * @param startSymbol The start symbol of the rule set that should not be removed. 
     * May be null if there is no start symbol
     * @return A simplified rule set.
     */
    public Set<IGeneralizedRule> simplifyRuleSet(
        Set<IGeneralizedRule> rules,
        List<Pair<String, ? extends RuleSet>> conversionLog,
        Abortion aborter,
        boolean allowOverapproximation,
        boolean filterFreeVarsFromCond,
        FunctionSymbol startSymbol,
        Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> combinedRulesMap
    ) {
        IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;
        if (LLVMDebuggingFlags.OUTPUT_RULES_BEFORE_SIMPLIFICATION) {
            LLVMProblem.logger.log(Level.FINE, "Rules for SCC:\n");
            for (IGeneralizedRule rule : rules) {
                LLVMProblem.logger.log(Level.FINE, rule + "\n");
            }
            LLVMProblem.logger.log(Level.FINE, "\n");
        }
        
        Set<FunctionSymbol> dontRemove = startSymbol == null ? Collections.emptySet() : Collections.singleton(startSymbol);

        // This combines rules and simplifies integer constraints.
        // Calling combineRules in a way such that DIV and MOD are not removed, as this could lead to exponential blowup of rule size
        Set<IGeneralizedRule> iRules = new RuleCombiner(rules, dontRemove, IDPPredefinedMap.DEFAULT_MAP, RoundingBehaviour.TOWARDS_ZERO, aborter, combinedRulesMap).combineRules(filterFreeVarsFromCond, true, false).y;

        conversionLog.add(new Pair<String, RuleSet>(
                "Combined rules. Obtained " + iRules.size() + " rules",
                new IGeneralizedRuleSet(iRules, null))
        );
        // Now run some filters on the obtained rules:
        ArgumentFilterResult resultPair = IntTRSDuplicateArgumentFilterProcessor.processRules(iRules, dontRemove);
        if (resultPair != null) {
            iRules = resultPair.x.x;
            conversionLog.add(
                new Pair<>(
                    "Filtered duplicate arguments:",
                    new RuleSet(ArgumentsRemovalProof.getFilterRules(resultPair.y, resultPair.x.y))
                )
            );
        }
        
        IGeneralizedRule.assertSetContainsRuleForFunctionSymbol(iRules, startSymbol);

        resultPair = IntTRSUnneededArgumentFilterProcessor.processRules(iRules, dontRemove, allowOverapproximation, null);
        if (resultPair != null) {
            iRules = resultPair.x.x;
            conversionLog.add(
                new Pair<>(
                    "Filtered unneeded arguments:",
                    new RuleSet(ArgumentsRemovalProof.getFilterRules(resultPair.y, resultPair.x.y))
                )
            );
        }
        
        IGeneralizedRule.assertSetContainsRuleForFunctionSymbol(iRules, startSymbol);
        
        //remove unused free variables from conditions
        Set<IGeneralizedRule> filteredRules = new LinkedHashSet<>();
        RemoveFreeVarsFromCond freeVarFilter = new RemoveFreeVarsFromCond(false);
        for (IGeneralizedRule rule : iRules) {
            filteredRules.add(freeVarFilter.removeFreeVarsFromCond(rule));
        }
        iRules = filteredRules;
        
        IGeneralizedRule.assertSetContainsRuleForFunctionSymbol(iRules, startSymbol);
        
        //These are an artifact of the rule combination.
        iRules = TerminationSCCToIDPv1Processor.removePredefinedOpsOnLhs(iRules, predefinedMap);
        IGeneralizedRule.assertSetContainsRuleForFunctionSymbol(iRules, startSymbol);
        
        if (LLVMDebuggingFlags.OUTPUT_RULES_AFTER_SIMPLIFICATION) {
            LLVMProblem.logger.log(Level.FINE, "Rules for SCC (after simplification):\n");
            for (IGeneralizedRule rule : iRules) {
                LLVMProblem.logger.log(Level.FINE, rule + "\n");
            }
            LLVMProblem.logger.log(Level.FINE, "\n");
        }
        return iRules;
    }
    
    /**
     * @param scc The SCC to convert.
     * @param conversionLog A log of things we have done to obtain the set of rules.
     * @param aborter The aborter that may tell us to stop.
     * @return A rule set corresponding to the input SCC.
     */
    public Set<IGeneralizedRule> translateSCCToRuleSet(
        SimpleGraph<LLVMAbstractState, LLVMEdgeInformation> scc,
        List<Pair<String, ? extends RuleSet>> conversionLog,
        Abortion aborter
    ) {
        return this.translateGraphToRuleSet(scc.getNodes(), scc.getEdges(), conversionLog, aborter).x;
    }
    
    /**
     * @param nodes The nodes in the graph to convert
     * @param edges The edges in the graph to convert
     * @param conversionLog A log of things we have done to obtain the set of rules.
     * @param aborter The aborter that may tell us to stop.
     * @return x: A rule set corresponding to the input SCC
     *         y: The map that maps the nodes in the LLVM graph to TRS functions
     */
    public Pair<Set<IGeneralizedRule>, Map<Node<LLVMAbstractState>, TRSFunctionApplication>> translateGraphToRuleSet(
        Set<Node<LLVMAbstractState>> nodes,
        Set<Edge<LLVMEdgeInformation, LLVMAbstractState>> edges,
        List<Pair<String, ? extends RuleSet>> conversionLog,
        Abortion aborter
    ) {
        assert nodes != null;
        assert edges != null;
        // convert states to functions, cache this for later use
        LinkedHashMap<Node<LLVMAbstractState>, TRSFunctionApplication> nodeMap =
            new LinkedHashMap<Node<LLVMAbstractState>, TRSFunctionApplication>();
        for (Node<LLVMAbstractState> actNode : nodes) {
            LLVMAbstractState actState = actNode.getObject();
            TRSFunctionApplication termEncoding = actState.toFunctionApplication(actNode.getNodeNumber(), null);
            nodeMap.put(actNode, termEncoding);
        }
        Set<IGeneralizedRule> inferredRules = new LinkedHashSet<IGeneralizedRule>();
        // edges to rules
        for (Edge<LLVMEdgeInformation, LLVMAbstractState> edge : edges) {
            IGeneralizedRule nextRule = this.inferRuleFromEdge(edge, nodeMap);
            if (nextRule != null) {
                inferredRules.add(nextRule);
            }
        }

        conversionLog.add(
            new Pair<String, RuleSet>(
                "Generated rules. Obtained " + inferredRules.size() + " rules",
                new IGeneralizedRuleSet(inferredRules, null)
            )
        );
        return new Pair<>(inferredRules, nodeMap);
    }

    /**
     * Parameters for this processor. Attributes must be public for our strategy framework.
     * @author cryingshadow
     * @version $Id$
     */
    public static class Arguments {

        /**
         * If set, we encode all knowledge on instance edges into the rules.
         */
        public LLVMInvariants useInvariants = LLVMInvariants.CHANGESANDINSTNONE;
        
        /**
         * If true, combining rules is allowed. Otherwise no rules are allowed to be combined
         */
        public boolean combineRules = true;
        
        /**
         * If true, using overapproximation is allowed. Otherwise overapproximation is not allowed
         */
        public boolean useOverapproximation = true;

    }

    /**
     * A very fine proof.
     * @author Marc Brockschmidt (don't blame me)
     */
    public abstract static class LLVMGraphToRulesProof extends DefaultProof {

        /**
         * Some documentation about the magic we've done.
         */
        private final List<Pair<String, ? extends RuleSet>> log;

        /**
         * Create the proof.
         * @param l Documentation about the magic we've done in the conversion.
         * @param shortN a short name for this proof (appears in the proof overview/navigation)
         * @param longN a long name for this proof (appears in the actual proof)
         */
        protected LLVMGraphToRulesProof(
            List<Pair<String, ? extends RuleSet>> l,
            String shortN,
            String longN
        ) {
            super();
            this.log = l;
            this.shortName = shortN;
            this.longName = longN;
        }

        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Transformed LLVM symbolic execution graph SCC into a rewrite problem. Log: ");
            sb.append(o.linebreak());
            for (Pair<String, ? extends RuleSet> entry : this.log) {
                sb.append(o.indent(entry.x));
                if (entry.y != null) {
                    sb.append(o.indent(entry.y.export(o)));
                } else {
                    sb.append(o.linebreak());
                }
            }
            return sb.toString();
        }
    }

}
