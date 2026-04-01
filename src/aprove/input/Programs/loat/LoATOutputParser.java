package aprove.input.Programs.loat;

import java.math.*;
import java.util.*;
import java.util.Map.*;
import java.util.regex.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import immutables.*;

/**
 * This class is used to exclusively parse the output provided by LoAT.
 * 
 * The most important (static) functions are:
 * finalGuard() -> returns the final guard simplified rule with the worst runtime (lower bound)
 * resultIsNonterm() -> whether LoAT could prove non-termination
 * retrieveRuleTree() -> retrieve a tree that captures all simplifications that LoAT applied during its proof
 * 
 * 
 * @author Constantin Mensendiek
 *
 */
public class LoATOutputParser {

    /**
     * parse the final guard of LoATs output
     * 
     * @param output the output provided by LoAT
     * @return a list of constraint
     */
    public static List<PlainIntegerRelation> finalGuard(List<String> output) {
        for (int i = output.size() - 1; i >= 0; i--) {
            String line = output.get(i).strip();
            if (line.startsWith("Rule guard: ")) {
                List<PlainIntegerRelation> relations = new LinkedList<>();
                String guard = line.substring(line.indexOf("[") + 1, line.indexOf("]"));
                if (!guard.trim().equals("")) {
                    for (String singleRel : guard.split("&&")) {
                        relations.add(intRelationOf(singleRel));
                    }
                }
                return relations;
            }
        }
        return null;
    }

    /**
     * Convert the input string to an integer relation recognized by Z3
     *
     * @param input the input string to be converted
     * @return the relation recognized by Z3
     */
    private static PlainIntegerRelation intRelationOf(String input) {
        String[] operands;
        IntegerRelationType relationType;

        if (input.contains("==")) {
            relationType = IntegerRelationType.EQ;
            operands = input.split("==");
        } else if (input.contains(">=")) {
            relationType = IntegerRelationType.GE;
            operands = input.split(">=");
        } else if (input.contains("<=")) {
            relationType = IntegerRelationType.LE;
            operands = input.split("<=");
        } else if (input.contains(">")) {
            relationType = IntegerRelationType.GT;
            operands = input.split(">");
        } else if (input.contains("<")) {
            relationType = IntegerRelationType.LT;
            operands = input.split("<");
        } else {
            throw new IllegalArgumentException("String relation cannot be parsed for further process, since relation type cannot be recognized.");
        }

        if (operands.length != 2) {
            throw new IllegalStateException("String relation cannot be parsed for further process.");
        }

        FunctionalIntegerExpression lhs = intExpressionOf(operands[0].trim());
        FunctionalIntegerExpression rhs = intExpressionOf(operands[1].trim());
        return new PlainIntegerRelation(relationType, lhs, rhs);
    }

    /**
     * Convert the input string to an integer expression recognized by Z3
     *
     * @param input the input string to be converted
     * @return the expression recognized by Z3
     */
    private static FunctionalIntegerExpression intExpressionOf(String input) {
        final String constRegExp = "-?\\d+";
        final String posVarRegExp = "[a-zA-Z_$]\\w*";
        final String negVarRegExp = "-[a-zA-Z_$]\\w*";
        final String varRegExp = "-?[a-zA-Z_$]\\w*";
        final String termExp = String.format("((%s|%s)\\*)*(%s|%s)", varRegExp, constRegExp, varRegExp, constRegExp);
        final String operatorExp = "[+\\-]";
        final String operationRegExp = String.format("(%s%s)+(%s)", termExp, operatorExp, termExp);

        if (input.matches(constRegExp)) {
            // for a constant, instantiate PlainIntegerConstant object directly
            return new PlainIntegerConstant(new BigInteger(input));
        } else if (input.matches(posVarRegExp)) {
            // for a variable, instantiate PlainIntegerVariable object directly
            return new PlainIntegerVariable(input);
        } else if (input.matches(negVarRegExp)) {
            // for a negated variable, instantiate PlainIntegerOperation object for unary operator
            return new PlainIntegerOperation(ArithmeticOperationType.NEG, new PlainIntegerVariable(input.substring(1)));
        } else if (input.matches(termExp)) {
            int operatorIndex = input.lastIndexOf('*');
            FunctionalIntegerExpression firstExpression = intExpressionOf(input.substring(0, operatorIndex));
            FunctionalIntegerExpression secondExpression = intExpressionOf(input.substring(operatorIndex + 1));
            return new PlainIntegerOperation(ArithmeticOperationType.MUL, firstExpression, secondExpression);
        } else if (input.matches(operationRegExp)) {
            // for an operation, instantiate PlainIntegerOperation object for binary operator

            // get the maximum last index of operators and get rid of the leading negation
            int lastIndexOfPlus = input.lastIndexOf('+');
            int lastIndexOfMinus = input.lastIndexOf('-');
            int operatorIndex = Math.max(lastIndexOfPlus, lastIndexOfMinus);

            // if the operation contains an addition with a negated variable or a negative integer
            if (lastIndexOfPlus + 1 == lastIndexOfMinus) {
                // then the addition should be treated as the operator
                operatorIndex = lastIndexOfPlus;
            }

            // process the operator
            ArithmeticOperationType operationType = null;
            char operator = input.charAt(operatorIndex);
            switch (operator) {
                case '+':
                    operationType = ArithmeticOperationType.ADD;
                    break;
                case '-':
                    operationType = ArithmeticOperationType.SUB;
                    break;
                default:
                    throw new IllegalStateException("Arithmetic operation type is not supported. " + operator);
            }

            // process the operands
            FunctionalIntegerExpression firstExpression = intExpressionOf(input.substring(0, operatorIndex));
            FunctionalIntegerExpression secondExpression = intExpressionOf(input.substring(operatorIndex + 1));
            return new PlainIntegerOperation(operationType, firstExpression, secondExpression);
        }

        throw new IllegalArgumentException("Input string cannot be converted to an expression. " + input);
    }

    /**
     * Convert the input string to an integer expression recognized by Z3
     *
     * @param input the input string to be converted
     * @return the expression recognized by Z3
     */
    private static TRSTerm termOf(String input) {
        input = input.trim();
        final String constRegExp = "-?\\d+";
        final String posVarRegExp = "[a-zA-Z_$]\\w*";
        final String negVarRegExp = "-[a-zA-Z_$]\\w*";
        final String varRegExp = "-?[a-zA-Z_$]\\w*";
        final String termExp = String.format("((%s|%s)\\*)*(%s|%s)", varRegExp, constRegExp, varRegExp, constRegExp);
        final String operatorExp = "[+\\-]";
        final String operationRegExp = String.format("(%s%s)+(%s)", termExp, operatorExp, termExp);

        if (input.matches(constRegExp)) {
            return TRSTerm.createConstant(input);
        } else if (input.matches(posVarRegExp)) {
            // for a variable, instantiate PlainIntegerVariable object directly
            return TRSTerm.createVariable(input);
        } else if (input.matches(negVarRegExp)) {
            // for a negated variable, instantiate PlainIntegerOperation object for unary operator
            return TRSTerm.createFunctionApplication(Func.UnaryMinus.asFunctionSymbol(),
                                                     TRSTerm.createVariable(input.substring(1)));
        } else if (input.matches(termExp)) {
            int operatorIndex = input.lastIndexOf('*');
            TRSTerm firstTerm = termOf(input.substring(0, operatorIndex));
            TRSTerm secondTerm = termOf(input.substring(operatorIndex + 1));
            return TRSTerm.createFunctionApplication(Func.Mul.asFunctionSymbol(), firstTerm, secondTerm);
        } else if (input.matches(operationRegExp)) {
            // for an operation, instantiate PlainIntegerOperation object for binary operator

            // get the maximum last index of operators and get rid of the leading negation
            int lastIndexOfPlus = input.lastIndexOf('+');
            int lastIndexOfMinus = input.lastIndexOf('-');
            int operatorIndex = Math.max(lastIndexOfPlus, lastIndexOfMinus);

            // if the operation contains an addition with a negated variable or a negative integer
            if (lastIndexOfPlus + 1 == lastIndexOfMinus) {
                // then the addition should be treated as the operator
                operatorIndex = lastIndexOfPlus;
            }

            // process the operator
            FunctionSymbol operationType = null;
            char operator = input.charAt(operatorIndex);
            switch (operator) {
                case '+':
                    operationType = Func.Add.asFunctionSymbol();
                    break;
                case '-':
                    operationType = Func.Sub.asFunctionSymbol();
                    break;
                default:
                    throw new IllegalStateException("Arithmetic operation type is not supported. " + operator);
            }

            // process the operands
            TRSTerm firstTerm = termOf(input.substring(0, operatorIndex));
            TRSTerm secondTerm = termOf(input.substring(operatorIndex + 1));
            return TRSTerm.createFunctionApplication(operationType, firstTerm, secondTerm);
        }

        throw new IllegalArgumentException("Input string cannot be converted to an expression. " + input);
    }

    /**
     * return whether LoAT succeeded in proving non-termination
     * 
     * @param output
     * @return
     */
    public boolean resultIsNonterm(List<String> output) {
        return output.get(output.size() - 1).equals("NO");
    }

    public void printInorder(Node root) {
        if (root != null) {
            System.out.println(root);
            printInorder(root.node1);

            printInorder(root.node2);
        }
    }

    /**
     * If the rule tree can be identified completely, return the rule tree of the complete proof
     * 
     * @param output LoAT's output
     * @return a tree with all applied simplifications
     */
    public static Optional<Node> retrieveRuleTree(List<String> output) throws AssertionError {
        List<String> strippedOutput = new LinkedList<>();
        for (String line : output) {
            strippedOutput.add(line.strip());
        }

        int indexPreprocessing = strippedOutput.indexOf("### Pre-processing the ITS problem ###");
        int indexSimplification = strippedOutput.indexOf("### Simplification by acceleration and chaining ###");
        int indexComplexity = strippedOutput.indexOf("### Computing asymptotic complexity ###");

        List<String> preprocessing = strippedOutput.subList(indexPreprocessing + 1, indexSimplification);
        List<String> simplification = strippedOutput.subList(indexSimplification + 1, indexComplexity);
        List<String> complexity = strippedOutput.subList(indexComplexity + 1, strippedOutput.size());

        // get nonterminating rule number
        String ruleNumber = null;
        for (String line : complexity) {
            if (line.startsWith("Computing asymptotic complexity for rule")) {
                String[] words = line.split(" ");
                ruleNumber = words[words.length - 1];
                break;
            }
        }
        assert ruleNumber != null;

        // get initial rules
        Map<String, Rule> initialRules = new HashMap<>();
        for (int i = preprocessing.indexOf("Initial linear ITS problem") + 2; i < preprocessing.size()
                                                                              && !preprocessing.get(i)
                                                                                               .equals(""); i++) {
            String line = preprocessing.get(i);
            int x = line.indexOf(':');
            initialRules.put(line.substring(0, x), new Rule(line));
        }

        // block-wisely reverse the simplification log
        List<List<String>> reversedSimplification = new LinkedList<>();

        List<Integer> indexEmptyLines = new LinkedList<>();
        for (int i = 0; i < simplification.size(); i++) {
            if (simplification.get(i).equals(""))
                indexEmptyLines.add(i);
        }

        for (int i = indexEmptyLines.size() - 2; i >= 0; i--) {
            reversedSimplification.add(simplification.subList(indexEmptyLines.get(i) + 1,
                                                              indexEmptyLines.get(i + 1)));
        }

        // parse
        Node root = new Node(ruleNumber);

        // collection of all nodes
        Map<String, Node> allRules = new HashMap<>();
        allRules.put(ruleNumber, root);
        // rules for which the definition is missing
        Map<String, Node> missingRules = new HashMap<>();
        missingRules.put(ruleNumber, root);
        // rules for which the creation instruction is missing
        Map<String, Node> missingChildren = new HashMap<>();
        missingChildren.put(ruleNumber, root);
        // rules which are potentially merged (same rules are combined) and thus need to be substituted with their original rule
        Map<String, Node> mergedRules = new HashMap<>();
        for (List<String> block : reversedSimplification) {
            if (missingChildren.isEmpty() && missingRules.isEmpty()) {
                break;
            }

            boolean ruleBlock = block.size() > 1 && block.get(1).startsWith("Start location:");

            // a block with rule definitions
            if (ruleBlock) {

                // if we need to look for merged rules
                if (!mergedRules.isEmpty()) {
                    for (String line : block.subList(2, block.size())) {
                        String ruleNum = line.substring(0, line.indexOf(':'));
                        String ruleDefintion = line.substring(line.indexOf(':') + 2);
                        for (Entry<String, Node> entry : mergedRules.entrySet()) {
                            Node n = entry.getValue();
                            if (n.rule.getRuleDefiniton().equals(ruleDefintion)) {
                                if (!ruleNum.equals(entry.getKey())) {
                                    n.rule.ruleString = line;
                                    missingChildren.put(ruleNum, n);
                                    missingChildren.remove(entry.getKey());
                                }
                            }
                        }
                    }
                    mergedRules.clear();
                }

                // normal iteration of the rule definitions
                for (String line : block.subList(2, block.size())) {
                    String rule = line.substring(0, line.indexOf(':'));
                    Node curNode = missingRules.get(rule);
                    if (curNode != null) {
                        curNode.rule.ruleString = line;
                        missingRules.remove(rule);
                    }
                    if (block.get(0).startsWith("Merged rules:")) {
                        curNode = missingChildren.get(rule);
                        if (curNode != null) {
                            mergedRules.put(rule, curNode);
                        }
                    }
                }
                // a block with rule creation instructions 
            } else {
                for (String line : block) {
                    int index = line.indexOf("new rule ");
                    String rule = line.substring(index + 9, line.length() - 1);
                    Node curNode = missingChildren.get(rule);
                    if (curNode != null) {
                        Pattern p = Pattern.compile("\\d+");
                        Matcher m = p.matcher(line);
                        List<String> numbers = new LinkedList<>();
                        while (m.find()) {
                            numbers.add(m.group());
                        }
                        if (line.startsWith("Chained")) {
                            assert numbers.size() == 3;
                            String rule1 = numbers.get(0);
                            String rule2 = numbers.get(1);
                            if (allRules.containsKey(rule1)) {
                                curNode.node1 = allRules.get(rule1);
                            } else if (initialRules.containsKey(rule1)) {
                                curNode.node1 = new Node(initialRules.get(rule1));
                                allRules.put(rule1, curNode.node1);
                            } else {
                                curNode.node1 = new Node(rule1);
                                missingRules.put(rule1, curNode.node1);
                                missingChildren.put(rule1, curNode.node1);
                                allRules.put(rule1, curNode.node1);
                            }

                            if (allRules.containsKey(rule2)) {
                                curNode.node2 = allRules.get(rule2);
                            } else if (initialRules.containsKey(rule2)) {
                                curNode.node2 = new Node(initialRules.get(rule2));
                                allRules.put(rule2, curNode.node2);
                            } else {
                                curNode.node2 = new Node(rule2);
                                missingRules.put(rule2, curNode.node2);
                                missingChildren.put(rule2, curNode.node2);
                                allRules.put(rule2, curNode.node2);
                            }
                            missingChildren.remove(rule);
                        } else if (line.startsWith("Accelerated")) {
                            assert numbers.size() == 2;
                            String rule1 = numbers.get(0);
                            if (initialRules.containsKey(rule1)) {
                                curNode.node1 = new Node(initialRules.get(rule1));
                                allRules.put(rule1, curNode.node1);
                            } else {
                                curNode.node1 = new Node(rule1);
                                missingRules.put(rule1, curNode.node1);
                                missingChildren.put(rule1, curNode.node1);
                                allRules.put(rule1, curNode.node1);
                            }
                            missingChildren.remove(rule);
                        } else {
                            //unknown
                        }
                    }
                }
            }
        }

        // check if all leaf are initial rules (otherwise generating a witness will not be possible)
        boolean treeIsComplete = checkLeafNodes(root, initialRules.keySet());
        if (!treeIsComplete) {
            System.err.println("The simplification tree is not complete. Thus, the witness cannot be generated.");
            return Optional.empty();
        }
        
        // parse only the initial rules
        List<Node> initialRuleNodes = collectLeafs(root);
        List<String> allVariables = new ArrayList<>();
        for (Node leaf : initialRuleNodes) {
            for (String var : leaf.rule.getAllBoundVariables()) {
                if (!allVariables.contains(var)) {
                    allVariables.add(var);
                }
            }
        }
        for (Node leaf : initialRuleNodes) {
            leaf.rule.parseRule(allVariables);
        }
        
        return Optional.of(root);
    }

    private static List<Node> collectLeafs(Node node) {
        List<Node> leaves = new ArrayList<>();
        if (node.node1 == null && node.node2 == null) {
            // leaf node
            leaves.add(node);
            return leaves;
        }
        
        // otherwise recursively check subtrees (if present)
        if (node.node1 != null) {
            leaves.addAll(collectLeafs(node.node1));
        }
        if (node.node2 != null) {
            leaves.addAll(collectLeafs(node.node2));
        }
        return leaves;
    }
    
    private static boolean checkLeafNodes(Node node, Set<String> initialRuleNames) {
        if (node.node1 == null && node.node2 == null) {
            // leaf node
            return initialRuleNames.contains(node.rule.getRuleNumber() + "");
        }
        
        // otherwise recursively check subtrees (if present)
        boolean subtree1 = true;
        boolean subtree2 = true;
        if (node.node1 != null) {
            subtree1 = checkLeafNodes(node.node1, initialRuleNames);
        }
        if (node.node2 != null) {
            subtree2 = checkLeafNodes(node.node2, initialRuleNames);
        }
        return subtree1 && subtree2;
    }

    // internal data structure
    public static class Rule {

        String ruleString;
        GeneralizedRule parsedRule;

        Rule(String ruleString) {
            this.ruleString = ruleString;
        }

        Rule() {
            this.ruleString = "no explicit definition";
        }

        // empty if nonterm as cost
        public Optional<TRSTerm> getCost() {
            String costString = ruleString.substring(ruleString.lastIndexOf(':') + 1);
            costString = costString.replace(".", "").strip(); // remove trailing dot
            if (costString.equalsIgnoreCase("nonterm")) {
                return Optional.empty();
            }
            return Optional.of(termOf(ruleString.substring(ruleString.lastIndexOf(':') + 1)));
        }
        
        public List<String> getAllBoundVariables() {
            List<String> vars = new ArrayList<>();
            Pattern pattern = Pattern.compile("k\\d+");
            Matcher matcher = pattern.matcher(ruleString);
            while (matcher.find()) {
               vars.add(matcher.group());
            }
            return vars;
        }
        
        public void parseRule(List<String> variables) {
            assert !ruleString.equals("no explicit definition");
            String str_rule = getRuleDefiniton();
            // source function symbol
            Pattern pattern = Pattern.compile("(f_\\d+)");
            Matcher matcher = pattern.matcher(ruleString);
            assert matcher.find();
            String source = matcher.group();
            // destination function symbol
            assert matcher.find();
            String destination = matcher.group();
            // updates
            String[] str_updates = str_rule.substring(matcher.end(), str_rule.indexOf("[")-2).split(",");
            Map<String,TRSTerm> updates = new HashMap<>();
            for (String update : str_updates) {
                int sep = update.indexOf("'");
                String key = update.substring(0,sep).trim();
                TRSTerm val = LoATOutputParser.termOf(update.substring(sep+2));
                updates.put(key, val);
            }
            // guard is ignored
            // create rule
            List<TRSVariable> vars = new ArrayList<>(variables.size());
            for (String var : variables) {
                vars.add(TRSTerm.createVariable(var));
            }
            FunctionSymbol src = FunctionSymbol.create(source, variables.size());
            TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(src, ImmutableCreator.create(vars));
            
            FunctionSymbol des = FunctionSymbol.create(destination, variables.size());
            List<TRSTerm> terms = new ArrayList<>(variables.size());
            for (String var : variables) {
                if (updates.containsKey(var)) {
                    terms.add(updates.get(var));
                }
                else {
                    terms.add(TRSTerm.createVariable(var));
                }
            }
            TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(des, ImmutableCreator.create(terms));
            this.parsedRule = GeneralizedRule.create(lhs, rhs);
        }

        public int getRuleNumber() {
            return Integer.parseInt(ruleString.substring(0, ruleString.indexOf(':')));
        }

        public String getRuleDefiniton() {
            return ruleString.substring(ruleString.indexOf(':') + 2);
        }
        
        public boolean nonterm() {
            return this.getCost().isEmpty();
        }

        @Override
        public String toString() {
            return this.ruleString;
        }

    }

    
    /**
     * 
     * Inner class that is used to store the rule tree.
     *
     */
    public static class Node {

        public Rule rule;
        public Node node1 = null;
        public Node node2 = null;

        Node(Rule rule) {
            this.rule = rule;
        }

        Node() {
            this.rule = new Rule();
        }

        public Node(String ruleNumber) {
            this.rule = new Rule(ruleNumber + ": not yet defined");
        }

        @Override
        public String toString() {
            String res = "";
            if (node1 == null) {
                res += "initial rule: ";
            } else if (node2 == null) {
                res += "accelerated rule: ";
            } else {
                res += "chained rule: ";
            }
            res += this.rule.toString();

            return res;
        }

        public String toShortString() {
            String res = "";
            if (node1 == null) {
                res += "initial rule: ";
                String sourceDestination = this.rule.getRuleDefiniton();
                res += this.rule.getRuleNumber()+": "+sourceDestination.substring(0, sourceDestination.indexOf(':')-1);
            } else if (node2 == null) {
                res += this.rule.nonterm() ? "nonterm " : "finitely ";
                res += "accelerated rule: "+this.rule.getRuleNumber();
            } else {
                res += "chained rule: "+this.rule.getRuleNumber();
            }

            return res;
        }
    }

}
