package aprove.input.Programs.loat;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.Map.*;
import java.util.function.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.input.Programs.loat.debug.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * 
 * Helper class for generating a violation witness where LoAT was used as a backend
 * This class contains implementation for both witness generation approaches for LoAT.
 * 
 * 1. Backtracking Variable Names:
 * copied some functions for witness generation from the T2Processor to make them available for the LoATProcessor
 * 
 * 2. Retracing Simplifications
 * 
 * @author Constantin Mensendiek
 *
 */
public class WitnessGenerationHelper {

    /**
     * 
     * This function is used to realize the RETRACING SIMPLIFICATIONS approach.
     * If this generation succeeds, the witness is returned.
     * 
     * @param obl 
     * @param varAssignMap
     * @param aborter
     * @param output
     */
    public static String generateFunctionSymbolList(BasicObligation obl,
                                                  Map<String, LLVMHeuristicConstRef> varAssignMap,
                                                  Abortion aborter,
                                                  List<String> output) throws AssertionError {
        Optional<LoATOutputParser.Node> opt_tree = LoATOutputParser.retrieveRuleTree(output);
        if (opt_tree.isEmpty())
            return null;
        LoATOutputParser.Node root = opt_tree.get();
        RuleTreeVisualizer.toDOT(root);
        List<IGeneralizedRule> rules = new LinkedList<IGeneralizedRule>(((KoatProblem) obl).getRules());

        // determine the starting term
        Map<TRSVariable, TRSTerm> substitution = new HashMap<>();
        for (String var : varAssignMap.keySet()) {
            BigInteger value = varAssignMap.get(var).getIntegerValue();
            TRSTerm substituteBy = TRSTerm.createConstant(value.abs().toString());
            if (value.signum() < 0) {
                substituteBy = TRSTerm.createFunctionApplication(Func.UnaryMinus.asFunctionSymbol(), substituteBy);
            }
            substitution.put(TRSTerm.createVariable(var), substituteBy);
        }
        TRSSubstitution guardSubstitution = TRSSubstitution.create(ImmutableCreator.create(substitution));
        TRSFunctionApplication startTerm = getFirstLeftChild(root).applySubstitution(guardSubstitution);
        
        // evaluate the rule tree
        List<Integer> int_tailPath = new LinkedList<>();
        List<Integer> int_loopPath = new LinkedList<>();
        evaluateRuleTree(root, startTerm, guardSubstitution, int_tailPath, int_loopPath, false);
        
        // map rule number sequence to actual rules
        List<IGeneralizedRule> tailPath = new LinkedList<>();
        for (int ruleNumber : int_tailPath) {
            tailPath.add(rules.get(ruleNumber));
        }
        List<IGeneralizedRule> loopPath = new LinkedList<>();
        for (int ruleNumber : int_loopPath) {
            loopPath.add(rules.get(ruleNumber));
        }
        
        // determine parent problem that combined rules in the ITS beforehand
        BasicObligation current = obl;
        while (current != null) {
            if (current instanceof CombinedRulesMap) {
                if (!((CombinedRulesMap) current).getCombinedRulesMap().isEmpty())
                    break;
            }
            current = current.getParent();
        }

        // de-combine rules in the tail and head with the found combinings
        if (current instanceof CombinedRulesMap) {
            Map<IGeneralizedRule, Pair<IGeneralizedRule, IGeneralizedRule>> combinedRulesMap =
                                                                                             ((CombinedRulesMap) current).getCombinedRulesMap();
            Map<Pair<String, String>, IGeneralizedRule> sourceDestinationOfOriginalRuleMap = new HashMap<>();
            Function<IGeneralizedRule, Pair<String, String>> retrieveSourceDestination = rule -> {
                String source = rule.getLeft().getRootSymbol().getName();
                String destination = ((TRSFunctionApplication) rule.getRule().getRight()).getRootSymbol().getName();
                return new Pair<>(source, destination);
            };
            for (IGeneralizedRule originalRule : combinedRulesMap.keySet()) {
                sourceDestinationOfOriginalRuleMap.put(retrieveSourceDestination.apply(originalRule), originalRule);
            }

            List<IGeneralizedRule> tailPath_decombined = new LinkedList<>(tailPath);
            List<IGeneralizedRule> loopPath_decombined = new LinkedList<>(loopPath);
            for (int i = 0; i < tailPath_decombined.size();) {
                IGeneralizedRule rule = tailPath_decombined.get(i);
                Pair<IGeneralizedRule, IGeneralizedRule> pair = null;
                if (combinedRulesMap.containsKey(rule)) {
                    pair = combinedRulesMap.get(rule);
                } else {
                    Pair<String, String> sourceDestination = retrieveSourceDestination.apply(rule);
                    if (sourceDestinationOfOriginalRuleMap.containsKey(sourceDestination)) {
                        pair = combinedRulesMap.get(sourceDestinationOfOriginalRuleMap.get(sourceDestination));
                    } else {
                        i++;
                        continue;
                    }
                }
                tailPath_decombined.set(i, pair.x);
                tailPath_decombined.add(i + 1, pair.y);
            }
            for (int i = 0; i < loopPath_decombined.size();) {
                IGeneralizedRule rule = loopPath_decombined.get(i);
                Pair<IGeneralizedRule, IGeneralizedRule> pair = null;
                if (combinedRulesMap.containsKey(rule)) {
                    pair = combinedRulesMap.get(rule);
                } else {
                    Pair<String, String> sourceDestination = retrieveSourceDestination.apply(rule);
                    if (sourceDestinationOfOriginalRuleMap.containsKey(sourceDestination)) {
                        pair = combinedRulesMap.get(sourceDestinationOfOriginalRuleMap.get(sourceDestination));
                    } else {
                        i++;
                        continue;
                    }
                }
                loopPath_decombined.set(i, pair.x);
                loopPath_decombined.add(i + 1, pair.y);
            }
            tailPath = tailPath_decombined;
            loopPath = loopPath_decombined;
        }

        // determine parent problem that converted the abstract states to function symbols
        current = obl;
        while (current != null) {
            if (current instanceof FunctionSymbolAbstractStateMap) {
                if (!((FunctionSymbolAbstractStateMap) current).getFunctionSymbolAbstractStateMap().isEmpty())
                    break;
            }
            current = current.getParent();
        }

        // get the function symbol to abstract states map
        Map<String, Node<LLVMAbstractState>> map = new HashMap<>();
        for (Entry<FunctionSymbol, Node<LLVMAbstractState>> e : ((FunctionSymbolAbstractStateMap) current).getFunctionSymbolAbstractStateMap()
                                                                                                          .entrySet()) {
            map.put(e.getKey().getName(), e.getValue());
        }

        // determine abstract states
        List<Node<LLVMAbstractState>> tailStates = new LinkedList<>();
        for (IGeneralizedRule rule : tailPath) {
            tailStates.add(map.get(rule.getLeft().getFunctionSymbol().getName()));
        }
        List<Node<LLVMAbstractState>> loopStates = new LinkedList<>();
        for (IGeneralizedRule rule : loopPath) {
            loopStates.add(map.get(rule.getLeft().getFunctionSymbol().getName()));
        }

        List<Node<LLVMAbstractState>> states = new LinkedList<>(tailStates);
        states.addAll(loopStates);

        // validate states are valid path in SEGraph
        // determine parent problem that combined rules in the ITS beforehand
        current = obl;
        while (current != null) {
            if (current instanceof LLVMSEGraphProblem) {
                break;
            }
            current = current.getParent();
        }
        assert current instanceof LLVMSEGraphProblem;
        LLVMSEGraph segraph = ((LLVMSEGraphProblem) current).getGraph();
        // check root
        assert segraph.getIn(tailStates.get(0)).isEmpty();
        // check complete path
        for (int i = 0; i < states.size() - 1; i++) {
            assert segraph.getOut(states.get(i)).contains(states.get(i + 1));
        }
        // check looping from last element in loop to first element in loop
        assert segraph.getOut(loopStates.get(loopStates.size() - 1)).contains(loopStates.get(0));

        // reduce states to distinct llvm lines
        LLVMProgramPosition previousPosition = tailStates.get(0).getObject().getProgramPosition();
        for (int i = 1; i < tailStates.size();) {
            LLVMProgramPosition currentPosition = tailStates.get(i).getObject().getProgramPosition();
            if (currentPosition.equals(previousPosition)) {
                tailStates.remove(i);
            } else {
                previousPosition = currentPosition;
                i++;
            }
        }
        for (int i = 0; i < loopStates.size();) {
            LLVMProgramPosition currentPosition = loopStates.get(i).getObject().getProgramPosition();
            if (currentPosition.equals(previousPosition)) {
                loopStates.remove(i);
                if (i == 0) {
                    loopStates.add(0, tailStates.remove(tailStates.size() - 1));
                    i++;
                }
            } else {
                previousPosition = currentPosition;
                i++;
            }
        }

        /*
        // find shortest llvm tail
        if (       loopStates.size()>1 
                && loopStates.get(0).getObject().getProgramPosition().equals(
                   loopStates.get(loopStates.size()-1).getObject().getProgramPosition())) {
            loopStates.remove(loopStates.size()-1);
        }
        do {
            LLVMProgramPosition lastTail = tailStates.get(tailStates.size()-1).getObject().getProgramPosition();
            LLVMProgramPosition lastLoop = loopStates.get(loopStates.size()-1).getObject().getProgramPosition();
            if (lastTail.equals(lastLoop)) {
                tailStates.remove(tailStates.size()-1);
                Node<LLVMAbstractState> lastLoopState = loopStates.remove(loopStates.size()-1);
                loopStates.add(0,lastLoopState);
            } else {
                break;
            }
        } while(true);
        */

        states = new LinkedList<>(tailStates);
        states.addAll(loopStates);

        // find branching decisions
        List<YNM> control = new LinkedList<>();
        for (int i = 0; i < states.size() - 1; i++) {
            LLVMAbstractState currentState = states.get(i).getObject();
            if (currentState.getCurrentInstruction() instanceof LLVMCondBrInstruction) {
                LLVMCondBrInstruction instr = (LLVMCondBrInstruction) currentState.getCurrentInstruction();
                LLVMAbstractState nextState = states.get(i + 1).getObject();
                if (instr.getIfTrueLabel().equals(nextState.getProgramPosition().y)) {
                    control.add(YNM.YES);
                } else if (instr.getIfFalseLabel().equals(nextState.getProgramPosition().y)) {
                    control.add(YNM.NO);
                } else {
                    // should never occur
                }
            }
        }

        // determine C states
        List<CState> tailC = new LinkedList<>();
        for (Node<LLVMAbstractState> node : tailStates) {
            tailC.add(node.getObject().toCState(node.getNodeNumber()));
        }
        List<CState> loopC = new LinkedList<>();
        for (Node<LLVMAbstractState> node : loopStates) {
            loopC.add(node.getObject().toCState(node.getNodeNumber()));
        }

        // reduce states to distinct C lines
        int previousLine = tailC.get(0).getCLine();
        for (int i = 1; i < tailC.size();) {
            int currentLine = tailC.get(i).getCLine();
            if (currentLine == -1 || currentLine == previousLine) {
                tailC.remove(i);
            } else {
                previousLine = currentLine;
                i++;
            }
        }
        for (int i = 0; i < loopC.size();) {
            int currentLine = loopC.get(i).getCLine();
            if (currentLine == -1 || currentLine == previousLine) {
                loopC.remove(i);
                if (i == 0) {
                    loopC.add(0, tailC.remove(tailC.size() - 1));
                    i++;
                }
            } else {
                previousLine = currentLine;
                i++;
            }
        }

        /*
        // split groups further if loop of one line is contained
        // can be determined if program positions within a group repeat and the direct predecessor is different (no refinement/instantiation state)
        // or if a node number/id is repeating
        Set<LLVMProgramPosition> positions = new HashSet<>();
        LLVMProgramPosition lastPosition = null;
        Set<Integer> nodeIds = new HashSet<>();
        for (int i = 0; i < states.size(); i++) {
            if (groupingIndices.contains(i)) {
                positions.clear();
                nodeIds.clear();
            }
            LLVMProgramPosition curPosition = states.get(i).getObject().getProgramPosition();
            int curId = states.get(i).getNodeNumber();
            if (!curPosition.equals(lastPosition) && positions.contains(curPosition) || nodeIds.contains(curId)) {
                groupingIndices.add(i);
                positions.clear();
                nodeIds.clear();
            }
            lastPosition = curPosition;
            positions.add(curPosition);
            nodeIds.add(curId);
        }
        Collections.sort(groupingIndices);*/

        // dump files for debugging
        RuleTreeVisualizer.toDOT(root);
        ReadableLLVMWitnessWriter.writeLLVMWitness(tailStates, loopStates);
        ReadableCWitnessWriter.writeCWitness(tailC, loopC);

        List<CState> cStates = new LinkedList<>(tailC);
        cStates.addAll(loopC);
        if (!loopC.get(0).equals(loopC.get(loopC.size() - 1)) || loopC.size() == 1) {
            cStates.add(loopC.get(0));
        }

        // write graphml file
        String programFile = Globals.programFile;
        File file = new File(programFile);
        String programHash = "";
        try {
            programHash = GraphMLFormatter.calcSHA256(file);
        } catch (Exception e) {
            e.printStackTrace();
        }
        StringBuilder graphmlWitness = new StringBuilder();
        graphmlWitness.append(GraphMLFormatter.init(programFile, programHash));
        graphmlWitness.append(GraphMLFormatter.sink());

        // write nodes
        boolean cycleReached = false;
        Set<Integer> nodeCreated = new HashSet<>();
        for (CState c : cStates) {
            if (!nodeCreated.contains(c.getNodeID())) {
                boolean cyclehead = false;
                graphmlWitness.append(GraphMLFormatter.createWitnessNode(c,
                                                                         cyclehead && !cycleReached));
                cycleReached |= cyclehead;
                nodeCreated.add(c.getNodeID());
            }
        }

        // write edges
        for (int i = 0; i < cStates.size() - 1; i++) {
            /*int index = groupingIndices.get(i);
            int nextIndex = groupingIndices.get(i + 1);
            YNM currentControl = YNM.MAYBE;
            if (needsControl(cStates.get(index).getSourceCode())) {
                if (!control.isEmpty()) {
                    currentControl = control.remove(0);
                    //graphmlWitness.append(GraphMLFormatter.createSinkEdge(cStates.get(index),YNM.invert(currentControl)));
                }else {
                    //System.out.println("control is empty although still needed");
                }
            
            }*/
            graphmlWitness.append(GraphMLFormatter.createWitnessEdge(cStates.get(i),
                                                                     cStates.get(i + 1),
                                                                     YNM.MAYBE));
        }

        graphmlWitness.append(GraphMLFormatter.finish());

        return graphmlWitness.toString();
    }

    /**
     * whether a node in the witness automaton will need a control annotation
     * 
     * @param sourceCode
     * @return
     */
    private static boolean needsControl(String sourceCode) {
        String code = sourceCode.replaceAll(" ", "");
        return (code.startsWith("while") && !code.startsWith("while(true)"))
               || code.startsWith("for")
               || code.startsWith("if")
               || code.startsWith("else if");
    }

    /**
     * get the leaf node that is most left starting from the "node" parameter
     * 
     * @param node
     * @param rules
     * @return
     */
    private static LoATOutputParser.Node getFirstLeftChildNode(LoATOutputParser.Node node) {
        // node is a leaf and thus an initial rule
        if (node.node1 == null && node.node2 == null) {
            return node;
        }
        // node is a chained or an accelerated rule
        else {
            return getFirstLeftChildNode(node.node1);
        }
    }
    
    /**
     * get the function symbol of the leaf node that is most left starting from the "node" parameter
     * 
     * @param node
     * @param rules
     * @return
     */
    private static TRSFunctionApplication getFirstLeftChild(LoATOutputParser.Node node) {
        return getFirstLeftChildNode(node).rule.parsedRule.getLeft();
    }

    /**
     * 
     * evaluating the rule tree. 
     * I.e. add configurations of the ITS to the tail or respectively the loop part of the lasso.
     * 
     * @param node
     * @param rules
     * @param current
     * @param tailPath
     * @param loopPath
     * @param nontermLoop
     * @return
     */
    public static TRSFunctionApplication
           evaluateRuleTree(LoATOutputParser.Node node,
                            TRSFunctionApplication current,
                            TRSSubstitution guardSubstitution,
                            List<Integer> tailPath,
                            List<Integer> loopPath,
                            boolean nontermLoop) throws AssertionError {
        // node is a leaf and thus an initial rule
        if (node.node1 == null && node.node2 == null) {
            if (nontermLoop)
                loopPath.add(node.rule.getRuleNumber());
            else
                tailPath.add(node.rule.getRuleNumber());
            return applyRule(node.rule.parsedRule, current, guardSubstitution);
        }
        // node is an accelerated rule
        else if (node.node2 == null) {
            int iterations;
            Optional<TRSTerm> cost = node.rule.getCost();
            boolean nonterm = false;
            if (cost.isEmpty()) {
                nonterm = true;
                iterations = 1;
            } else {
                TRSSubstitution sub = getSubstitution(getFirstLeftChild(node).getArguments(),
                                                      current.getArguments()).compose(guardSubstitution);
                // evaluate cost term of parent
                BigInteger evaluatedCostParent = evaluateTerm(cost.get().applySubstitution(sub));
                int iterations_parent = evaluatedCostParent.intValue();
                // evaluate cost term of child
                BigInteger evaluatedCostChild = evaluateTerm(node.node1.rule.getCost().get().applySubstitution(sub));
                int iterations_child = evaluatedCostChild.intValue();

                assert (iterations_parent % iterations_child == 0);
                iterations = iterations_parent / iterations_child;
            }
            TRSFunctionApplication next = current;
            for (int i = 0; i < iterations; i++) {
                next = evaluateRuleTree(node.node1, next, guardSubstitution, tailPath, loopPath, nonterm);
            }
            return next;
        }
        // node is a chained rule
        else {
            TRSFunctionApplication next = evaluateRuleTree(node.node1, current, guardSubstitution, tailPath, loopPath, nontermLoop);
            return evaluateRuleTree(node.node2, next, guardSubstitution, tailPath, loopPath, nontermLoop);
        }
    }

    /**
     * given a configuration: apply a rule
     * 
     * @param rule the rule to be applied
     * @param current the current configuration
     * @return the configuration after applying the rule
     */
    private static TRSFunctionApplication applyRule(GeneralizedRule rule, TRSFunctionApplication current, TRSSubstitution guardSubstitution) throws AssertionError {
        List<TRSTerm> args = rule.getLeft().getArguments();

        assert rule.getLeft().getFunctionSymbol().equals(current.getFunctionSymbol())
               && args.size() == current.getArity() : "current rule cannot be applied";

        TRSSubstitution substitution = getSubstitution(args, current.getArguments());

        TRSFunctionApplication rhs = (TRSFunctionApplication) rule.getRight();

        FunctionSymbol rf = rhs.getFunctionSymbol();

        List<TRSTerm> evaluatedArgs = new LinkedList<>();
        for (TRSTerm arg : rhs.getArguments()) {
            TRSTerm currentTerm = arg.applySubstitution(guardSubstitution);
            currentTerm = currentTerm.applySubstitution(substitution);
            if (currentTerm.isGroundTerm()) {
                currentTerm = TRSTerm.createConstant(evaluateTerm(currentTerm).toString());
            }
            evaluatedArgs.add(currentTerm);
        }

        TRSFunctionApplication next = TRSTerm.createFunctionApplication(rf, ImmutableCreator.create(evaluatedArgs));
        return next;
    }

    /**
     * creates a object of TRSSubstitution that replaced the entries of the first list by the entries of the second one.
     * @param list1
     * @param list2
     * @return
     */
    private static TRSSubstitution getSubstitution(List<TRSTerm> list1, List<TRSTerm> list2) throws AssertionError {
        assert list1.size() == list2.size();
        Map<TRSVariable, TRSTerm> map = new HashMap<>(list1.size());
        for (int i = 0; i < list1.size(); i++) {
            map.put((TRSVariable) list1.get(i), list2.get(i));
        }
        return TRSSubstitution.create(ImmutableCreator.create(map));
    }

    /**
     * calculate the correct (no bitvector, i.e. BigInteger) value for a term
     * @param currentTerm
     * @return
     */
    private static BigInteger evaluateTerm(TRSTerm currentTerm) throws AssertionError {
        assert currentTerm instanceof TRSConstantTerm
               || currentTerm instanceof TRSCompoundTerm : "A variable is not evaluable: "+currentTerm.toString();

        if (currentTerm instanceof TRSConstantTerm) {
            return new BigInteger(((TRSConstantTerm) currentTerm).getValue());
        } else {
            TRSCompoundTerm compound = (TRSCompoundTerm) currentTerm;
            if (compound.getArguments().size() == 1 && compound.getName().equals(Func.UnaryMinus.getName())) {
                return evaluateTerm(compound.getArgument(0)).negate();
            }
            BiFunction<BigInteger, BigInteger, BigInteger> operator = null;
            switch (compound.getName()) {
                case "+":
                    operator = ((x, y) -> x.add(y));
                    break;
                case "-":
                    operator = ((x, y) -> x.subtract(y));
                    break;
                case "*":
                    operator = ((x, y) -> x.multiply(y));
                default:
                    break;
            }
            return operator.apply(evaluateTerm(compound.getArgument(0)), evaluateTerm(compound.getArgument(1)));
        }
    }

    /**
     * Get the lasso problem of the current termination problem
     *
     * @param currentProblem the current termination problem
     * @return the lasso problem of the current termination problem if the lasso problem is found, null otherwise
     */
    private static BasicObligation getGraphProblem(BasicObligation currentProblem) {
        BasicObligation currentObligation = currentProblem;

        while (currentObligation.getParent() != null) {
            if (currentObligation instanceof LLVMLassoProblem || currentObligation instanceof LLVMSEGraphProblem) {
                return currentObligation;
            }
            currentObligation = currentObligation.getParent();
        }

        return null;
    }

    /**
     * Get the variable assignment in lasso problem for the current termination problem
     *
     * @param currentProblem the current termination problem
     * @param varAssign the variable assignment in current termination problem
     * @return the variable assignment in lasso problem
     */
    private static Map<String, LLVMHeuristicConstRef>
            getLassoVariableAssignment(BasicObligation currentProblem, Map<String, LLVMHeuristicConstRef> varAssign) {
        Map<String, LLVMHeuristicConstRef> resultVarAssign = new HashMap<>();

        varAssign.forEach((key, value) -> {
            getLassoVariables(currentProblem, key)
                                                  .forEach(originalVar -> resultVarAssign.put(originalVar, value));
        });

        return resultVarAssign;
    }

    /**
     * Get the variables in lasso problem for the current termination problem
     *
     * @param currentProblem  the current termination problem
     * @param currentVariable the variable in current termination problem
     * @return the variables in lasso problem
     */
    private static List<String> getLassoVariables(BasicObligation currentProblem, String currentVariable) {
        if (currentProblem == null) {
            throw new IllegalArgumentException("Current problem cannot be null.");
        }

        BasicObligation currentObligation = currentProblem;
        List<String> foundKeyPre = new LinkedList<>(); // keys found in the previous round
        List<String> foundKeyPost = new LinkedList<>(); // keys found in the current round according to the keys found in the previous round
        foundKeyPre.add(currentVariable);

        do {
            // if current obligation contains variable renaming, get the key according to the value
            if (currentObligation instanceof VariableRenaming) {
                ((VariableRenaming) currentObligation).getVariableRenaming()
                                                      .forEach((key, value) -> {
                                                          foundKeyPre.forEach(keyPre -> {

                                                              // if the key is found in the current round, add it to the post list
                                                              if (value.contains(keyPre)) {
                                                                  foundKeyPost.add(key);
                                                              }

                                                          });
                                                      });
                // if a key from the previous round is not found after iterating over the current variable renaming,
                // it means the variable renaming from that key only happens in the previous round
                // and the back tracking of that key is omitted in the current round

                // move the keys in post list to pre list
                foundKeyPre.clear();
                foundKeyPre.addAll(foundKeyPost);
                foundKeyPost.clear();
            }

            // if the target problem is reached, return the result directly
            // if the the current obligation is not a lasso but the parent is a graph, a strategy is used where the whole graph is transformed to an ITS
            if (currentObligation.getClass() == LLVMLassoProblem.class
                || currentObligation.getParent() instanceof LLVMSEGraphProblem) {
                return foundKeyPre;
            }

            currentObligation = currentObligation.getParent();
        } while (currentObligation != null);
        return foundKeyPre;
    }

    public static String
           generateWitness(BasicObligation obligation, Map<String, LLVMHeuristicConstRef> varAssign, Abortion aborter) {
        // if no variable assignment in lasso is found, stop generating immediately
        if (varAssign == null || varAssign.isEmpty()) {
            return null;
        }

        BasicObligation graphProblem = getGraphProblem(obligation);
        if (graphProblem != null) {
            Map<String, LLVMHeuristicConstRef> lassoVarAssign = getLassoVariableAssignment(obligation, varAssign);
            if (graphProblem instanceof LLVMLassoProblem) {
                return ((LLVMLassoProblem) graphProblem).buildGraphMLWitness(lassoVarAssign, aborter);
            } else if (graphProblem instanceof LLVMSEGraphProblem) {
                return ((LLVMSEGraphProblem) graphProblem).buildGraphMLWitness(lassoVarAssign, aborter);
            }
        }
        return null;
    }
}
