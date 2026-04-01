package aprove.input.Programs.impact;

import java.util.*;

import aprove.input.Generated.impact.analysis.*;
import aprove.input.Generated.impact.node.*;
import aprove.input.Programs.impact.GTP.*;
import aprove.input.Programs.impact.GTP.nodes.*;
import aprove.input.Programs.impact.GTP.nodes.VariableNode.*;
import aprove.input.Programs.impact.Program.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Convert to a GtpProgram
 * @author marinag
 */
public class Converter extends DepthFirstAdapter {
    /**
     * Functions declarations info
     */
    private final HashMap<String, FunctionDeclaration> functionDeclarations;

    /**
     * Global variables
     */
    private final HashSet<String> globals;

    //  private boolean isDone = false;

    private ArrayList<CommandNode> commands = null;
    private final Stack<Block> commandBlocks = new Stack<>();
    private final Stack<TId> calls = new Stack<>();

    private String currentFunction = null;
    private final Stack<BooleanExpressionNode> expressions = new Stack<>();
    private final Stack<Triple<VariableNode, NumericExpressionNode, String>> assignments = new Stack<>();


    private int callCounter = 0;
    private int arrayEntryCounter = 0;

    private int idCounter = 0;

    private final ArrayList<Pair<VariableNode, NumericExpressionNode>> variablesDeclarations = new ArrayList<>();

    /**
     * The position of the branching to the main function (possibly after global variables declaration)
     */
    private int branchToMain = 0;


    /**
     * @param functionDeclarations
     * @param globals
     */
    public Converter(final HashMap<String, FunctionDeclaration> functionDeclarations, final HashSet<String> globals) {
        this.functionDeclarations = functionDeclarations;
        this.globals = globals;
    }

    /**
     * @param commands l- list of commands
     * @return refined list of commands, after the removal of redundant commands
     */
    private static ArrayList<CommandNode> refine(final ArrayList<CommandNode> commands) {
        final ArrayList<CommandNode> result = new ArrayList<>();

        final int len = commands.size();

        for (int i=0; i<len; i++) {
            CommandNode command = commands.get(i);

            if (command instanceof NoOperationCommandNode && command.getLabel() == null) {
                continue;
            }

            if (command instanceof NoOperationCommandNode
                && command.getLabel() != null
                && i < (len - 1)
                && commands.get(i + 1).getLabel() == null)
            {
                command = commands.get(i + 1);
                command.setLabel(commands.get(i).getLabel());
                i++;
            }

            result.add(command);
        }

        return result;
    }


    @SuppressWarnings("javadoc")
    private void addToCurrentBlock(final CommandNode command) {
        this.commandBlocks.peek().addCommand(command);
    }

    @SuppressWarnings("javadoc")
    private void addToCurrentBlock(final int index, final CommandNode command) {
        this.commandBlocks.peek().addCommand(index, command);
    }

    @SuppressWarnings("javadoc")
    private void addAllToCurrentBlock(final ArrayList<CommandNode> commands) {
        this.commandBlocks.peek().addAllCommands(commands);
    }

    /**
     * Set whether the current block has a return statement at all paths or no
     * @param value
     */
    private void setCurrentRetunStatememt(final boolean value) {
        this.commandBlocks.peek().setReturnValueStatement(value);
    }

    //    private void setNextLabel(final String label) {
    //        this.addToCurrentBlock(new NoOperationCommandNode(" ", 0, 0, label));
    //        this.currentBlock().setRecentOriginalText("NOP");
    //    }

    @SuppressWarnings("javadoc")
    public Block currentBlock() {
        if (this.commandBlocks.isEmpty()) {
            return null;
        }

        return this.commandBlocks.peek();
    }

    private FunctionDeclaration currentFunctionDeclaration() {
        if (this.currentFunction == null) {
            return null;
        }

        return this.functionDeclarations.get(this.currentFunction);
    }

    /**
     * Pop current block from blocks stack
     * @return list of commands at current block
     */
    private ArrayList<CommandNode> extractCurrentBlock() {
        return this.commandBlocks.pop().getCommands();
    }

    /**
     * Pop current block from blocks stack and add its commands to the father block
     * @return list of commands at (new) current block
     */
    private ArrayList<CommandNode> extractCurrentToFather() {
        final ArrayList<CommandNode> commands = this.extractCurrentBlock();
        this.currentBlock().addAllCommands(commands);

        return this.currentBlock().getCommands();
    }


    /**
     * @return GO-TO program
     * @throws ConvertException in case conversion was not yet completed
     */
    public GtpProgram getGtpProgram() throws ConvertException {
        if (this.commands == null) {
            throw new ConvertException(0, 0, "Program not done");
        }

        return new GtpProgram(this.commands);
    }

    @Override
    public String toString() {
        final StringBuilder builder = new StringBuilder();
        int counter = 0;
        for (final CommandNode comm : this.commands) {
            builder.append("[" + String.valueOf(counter++) + "]\t");
            builder.append(comm.toString());
            builder.append("\n");
        }
        return builder.toString();
    }

    @Override
    public void inAProgram(final AProgram node) {
        final FunctionDeclaration mainDeclaration = this.functionDeclarations.get(Converter.MAIN_FUNCTION);

        if (mainDeclaration == null) {
            throw new ConvertException(0, 0, "Missing main function");
        }

        this.inBlock(LabelNode.Type.NONE, null);

        for (final String var : mainDeclaration.getParams()) {
            this.addToCurrentBlock(new PushCommandNode("", 0, 0, null, new VariableNode(
                "",
                0,
                0,
                var,
                Converter.MAIN_FUNCTION,
                VariableNode.Type.PARAMTER)));
        }

        this.addToCurrentBlock(new CallCommandNode("", 0, 0, "", new LabelNode(
            Converter.MAIN_FUNCTION,
            LabelNode.Type.FUNCTION_BEGIN,
            0), Converter.MAIN_FUNCTION));

        this.addToCurrentBlock(new StopCommandNode("", 0, 0, ""));
    }

    @Override
    public void outAProgram(final AProgram node) {
        this.commands = Converter.refine(this.currentBlock().getCommands());
    }

    @Override
    public void outALabel(final ALabel node) {
        final TId id = node.getId();

        this.setNextLabel(new LabelNode(
            id.getText() + " " + node.getCol().getText(),
            id.getLine(),
            id.getPos(),
            this.currentFunction,
            LabelNode.Type.USER_DEFINED,
            id.getText()));
    }

    private NumericExpressionNode popNumericExpression() {
        final BooleanExpressionNode exp = this.expressions.pop();

        if (exp instanceof NumericExpressionNode) {
            return (NumericExpressionNode) exp;
        }

        throw new ConvertException(exp.getLine(), exp.getPos(), "Numeric expression expected: " + exp.getText());
    }

    private VariableNode popVariable() {
        final BooleanExpressionNode exp = this.expressions.pop();

        try {
            if (exp instanceof NumericExpressionNode) {
                return (VariableNode)exp;
            }
        } catch (final ConvertException e) {
        }

        throw new ConvertException(exp.getLine(), exp.getPos(), "Variable expected: " + exp.getText());
    }

    @Override
    public void outAMinusNumericUnary (final AMinusNumericUnary node) {
        final NumericExpressionNode exp =this.popNumericExpression();

        this.expressions.push(new NegatedNumericExpressionNode(node.toString(), node.getMinus().getLine(), node
            .getMinus()
            .getPos(), exp));
    }

    @Override
    public void outAArrayItem(final AArrayItem node) {

        final NumericExpressionNode index = this.popNumericExpression();
        final VariableNode array = this.popVariable();

        final String id = String.valueOf(this.arrayEntryCounter++);

        final VariableNode indexVar =
            new VariableNode(index.getText(), index.getLine(), index.getPos(), id, this.currentFunction, Type.INDEX);

        final NumericExpressionNode indexExp =
            new BinrayNumericExpressionNode(
                array.getText(),
                array.getLine(),
                array.getPos(),
                array,
                index,
                BinrayNumericExpressionNode.Type.ADD);

        this.addToCurrentBlock(
            new AssignCommandNode(
                array.getText(),
                array.getLine(),
                array.getPos(),
                null,
                indexVar,
                indexExp));

        final VariableNode arrayEntry =
            new VariableNode(index.getText(), index.getLine(), index.getPos(), id, this.currentFunction, Type.ARRAY);

        this.currentBlock().addVariable(arrayEntry);

        this.expressions.push(arrayEntry);
    }

    @Override
    public void outAEqualityBooleanPrimary(final AEqualityBooleanPrimary node) {
        final NumericExpressionNode expA = this.popNumericExpression();
        final NumericExpressionNode expB = this.popNumericExpression();

        this.expressions.push(new BinaryBooleanExpressionNode(
            node.toString(),
            expB.getLine(),
            expB.getPos(),
            expA,
            expB,
            BinaryBooleanExpressionNode.Type.EQUAL));
    }

    @Override
    public void outAInequalityBooleanPrimary(final AInequalityBooleanPrimary node) {
        final NumericExpressionNode expA = this.popNumericExpression();
        final NumericExpressionNode expB = this.popNumericExpression();

        this.expressions.push(new ComplexBooleanExpressionNode(
            "",
            0,
            0,
            new BinaryBooleanExpressionNode(
                node.toString(),
                expB.getLine(),
                expB.getPos(),
                expA,
                expB,
                BinaryBooleanExpressionNode.Type.GREATER),
                new BinaryBooleanExpressionNode(
                    node.toString(),
                    expB.getLine(),
                    expB.getPos(),
                    expB,
                    expA,
                    BinaryBooleanExpressionNode.Type.GREATER),
                    ComplexBooleanExpressionNode.Type.OR));
    }

    @Override
    public void outALessBooleanPrimary(final ALessBooleanPrimary node) {
        final NumericExpressionNode expA = this.popNumericExpression();
        final NumericExpressionNode expB = this.popNumericExpression();

        this.expressions.push(new BinaryBooleanExpressionNode(
            node.toString(),
            expB.getLine(),
            expB.getPos(),
            expA,
            expB,
            BinaryBooleanExpressionNode.Type.GREATER));
    }

    @Override
    public void outAGreaterBooleanPrimary(final AGreaterBooleanPrimary node) {
        final NumericExpressionNode expA = this.popNumericExpression();
        final NumericExpressionNode expB = this.popNumericExpression();

        this.expressions.push(new BinaryBooleanExpressionNode(
            node.toString(),
            expB.getLine(),
            expB.getPos(),
            expB,
            expA,
            BinaryBooleanExpressionNode.Type.GREATER));
    }

    @Override
    public void outALequalBooleanPrimary(final ALequalBooleanPrimary node) {
        final NumericExpressionNode expA = this.popNumericExpression();
        final NumericExpressionNode expB = this.popNumericExpression();

        this.expressions.push(new BinaryBooleanExpressionNode(
            node.toString(),
            expB.getLine(),
            expB.getPos(),
            expA,
            expB,
            BinaryBooleanExpressionNode.Type.GREATER_EQ));
    }

    @Override
    public void outAGequalBooleanPrimary(final AGequalBooleanPrimary node) {
        final NumericExpressionNode expA = this.popNumericExpression();
        final NumericExpressionNode expB = this.popNumericExpression();

        this.expressions.push(new BinaryBooleanExpressionNode(
            node.toString(),
            expB.getLine(),
            expB.getPos(),
            expB,
            expA,
            BinaryBooleanExpressionNode.Type.GREATER_EQ));
    }

    @Override
    public void outAFalseBooleanConst(final AFalseBooleanConst node) {
        this.expressions.push(new ConstantBooleanExpressionNode(node.toString(), node.getFalse().getLine(), node
            .getFalse()
            .getPos(), false));
    }

    @Override
    public void outATrueBooleanConst(final ATrueBooleanConst node) {
        this.expressions.push(new ConstantBooleanExpressionNode(node.toString(), node.getTrue().getLine(), node
            .getTrue()
            .getPos(), true));
    }

    @Override
    public void outAConjunctionBooleanTerm(final AConjunctionBooleanTerm node) {
        final BooleanExpressionNode expA = this.expressions.pop();
        final BooleanExpressionNode expB = this.expressions.pop();

        this.expressions.push(new ComplexBooleanExpressionNode(
            node.toString(),
            expB.getLine(),
            expB.getPos(),
            expB,
            expA,
            ComplexBooleanExpressionNode.Type.AND));

    }

    @Override
    public void outADisjunctionBooleanExp(final ADisjunctionBooleanExp node) {
        BooleanExpressionNode expA = this.expressions.pop();
        final BooleanExpressionNode expB = this.expressions.pop();

        expA =
            new ComplexBooleanExpressionNode(
                node.toString(),
                expA.getLine(),
                expA.getPos(),
                expB.negate(),
                expA,
                ComplexBooleanExpressionNode.Type.AND);

        this.expressions.push(new ComplexBooleanExpressionNode(
            node.toString(),
            expB.getLine(),
            expB.getPos(),
            expB,
            expA,
            ComplexBooleanExpressionNode.Type.OR));

    }

    @Override
    public void inAFunctionId(final AFunctionId node) {
        this.currentFunction = node.getId().getText();
    }

    @Override
    public void outAFunctionDeclaration(final AFunctionDeclaration node) {
        this.currentFunction = null;
    }

    @Override
    public void outAFunctionDefinition(final AFunctionDefinition node) {
        this.currentFunction = null;
    }

    @Override
    public void outAExternalDeclaration(final AExternalDeclaration node) {
        if (this.currentFunction.indexOf(Converter.ALLOWED_EXTERNAL_PREFIX) != 0) {
            throw new ConvertException(0, 0, "Uknown external: " + this.currentFunction);
        }

        this.currentFunction = null;
    }

    private void addVariableDeclaration(final NumericExpressionNode assign) {
        final VariableNode var = this.popVariable();

        this.variablesDeclarations.add(new Pair<>(var, assign));
    }

    @Override
    public void outAMultipleVariablesDeclarationList(final AMultipleVariablesDeclarationList node) {
        NumericExpressionNode assign = null;

        if (node.getAssignmentPostfix() != null) {
            assign = this.popNumericExpression();
        } else {
            final String name = "?" + Converter.COEF_COUNTER++;
            final VariableNode ndtVar =
                new VariableNode(
                    node.toString(),
                    0, 0,
                    null,
                    this.currentFunction,
                    Type.NONDET);

            this.currentBlock().addVariable(ndtVar);
            assign = ndtVar;

            // assign = new VariableNode("NDT", 0, 0, null, this.currentFunction, Type.NONDET);
        }

        this.addVariableDeclaration(assign);
    }

    @Override
    public void outASingleVariablesDeclarationList(final ASingleVariablesDeclarationList node) {
        NumericExpressionNode assign = null;

        if (node.getAssignmentPostfix() != null) {
            assign = this.popNumericExpression();
        } else {
            final String name = "?" + Converter.COEF_COUNTER++;
            final VariableNode ndtVar =
                new VariableNode(
                    node.toString(),
                    0, 0,
                    null,
                    this.currentFunction,
                    Type.NONDET);

            this.currentBlock().addVariable(ndtVar);
            assign = ndtVar;

            //  assign = new VariableNode("NDT", 0, 0, null, null, Type.NONDET);
        }

        this.addVariableDeclaration(assign);
    }

    @Override
    public void outAVariableDeclaration(final AVariableDeclaration node) {
        for (final Pair<VariableNode, NumericExpressionNode> p : this.variablesDeclarations) {

            final VariableNode var = p.x;
            final NumericExpressionNode assign = p.y;

            //        NumericExpressionNode assign = null;

            //        if (node.getAssignmentPostfix() != null) {
            //            assign = this.expressions.pop();
            //        } else {
            //            assign = new VariableNode("NDT", 0, 0, null, null, Type.NONDET);
            //        }

            //        final VariableNode var = this.popVariable();


            //if (assign != null) {
            final CommandNode assignCmd =
                new AssignCommandNode(
                    node.toString(),
                    var.getLine(),
                    var.getPos(),
                    null,
                    var,
                    assign);

            assignCmd.setOriginalText(node.toString());

            if (this.currentFunction == null) {
                this.addToCurrentBlock(this.branchToMain++, assignCmd);
            } else {
                this.addToCurrentBlock(assignCmd);
            }
            //  }

            this.currentBlock().addVariable(var);
        }

        this.variablesDeclarations.clear();
    }

    @Override
    public void inAFunctionBody(final AFunctionBody node) {
        this.callCounter = 0;
        this.inBlock(LabelNode.Type.FUNCTION_BEGIN, this.currentFunction);


        final ArrayList<String> param = this.functionDeclarations.get(this.currentFunction).getParams();
        //  Collections.reverse(param);
        for (final String p : param) {

            final VariableNode varP = new VariableNode(
                p,
                0,
                0,
                p,
                this.currentFunction,
                Type.PARAMTER);

            final VariableNode var = new VariableNode(
                p,
                0,
                0,
                p,
                this.currentFunction,
                Type.VARIABLE);

            this.addToCurrentBlock(new PopCommandNode("", 0, 0, null, var));
            // this.addToCurrentBlock(new AssignCommandNode("", 0, 0, null, var, varP));

            this.currentBlock().addVariable(var);
        }
    }

    @Override
    public void outAFunctionBody(final AFunctionBody node) {
        final String callId = this.currentFunction;

        this.setNextLabel(new LabelNode(this.currentFunction, LabelNode.Type.FUNCTION_END, 0));


        if (this.currentFunction.equals(Converter.MAIN_FUNCTION)) {
            this.addToCurrentBlock(new StopCommandNode("", node.getBracR().getLine(), node.getBracR().getPos(), null));

            this.currentBlock().setRecentOriginalText("STOP");
        } else {
            this.addToCurrentBlock(
                new ReturnCommandNode(
                    "",
                    node.getBracR().getLine(),
                    node.getBracR().getPos(),
                    null,
                    callId));

            this.currentBlock().setRecentOriginalText("RETURN");
        }

        /* DEBUG
        if (!this.currentBlock().hasReturnValueStatement()) {
            throw new RuntimeException(this.currentFunction + ":  not all paths have a return value");
        }*/

        this.currentFunction = null;

        this.extractCurrentToFather();
    }

    @Override
    public void inACallId(final ACallId node) {
        this.calls.push(node.getId());

        final String callId = node.getId().getText();

        if (!this.functionDeclarations.keySet().contains(callId)
            && callId.indexOf(Converter.ALLOWED_EXTERNAL_PREFIX) != 0)
        {
            throw new ConvertException(node.getId().getLine(), node.getId().getPos(), "Call of undefined function: "
                + callId);
        }
    }

    //    @Override
    //    public void outALabelId(final ALabelId node) {
    //        this.branch = node.getId();
    //
    //        final String branchId = this.branch.getText();
    //
    //        if (!this.currentFunction().hasLabel(branchId)) {
    //            throw new ConvertException(node.getId().getLine(), node.getId().getPos(), "Undefined label: " + branchId);
    //        }
    //    }

    @Override
    public void outAGotoSimpleStatement(final AGotoSimpleStatement node) {

        final String id = node.getLabelId().toString().trim();

        if (!this.currentFunctionDeclaration().hasLabel(id)) {
            throw new ConvertException(node.getGoto().getLine(), node.getGoto().getPos(), "Branch to undefined label: "
                + id);
        }

        final LabelNode label =
            new LabelNode(
                this.currentFunction,
                0, 0,
                this.currentFunction,
                LabelNode.Type.USER_DEFINED,
                id);

        this.addToCurrentBlock(new BranchCommandNode(
            node.getGoto().getText() + " " + id,
            node.getGoto().getLine(),
            node.getGoto().getPos(),
            null,
            label));

    }


    @Override
    public void outAFunctionCall(final AFunctionCall node) {
        final String callId = this.calls.peek().getText();

        if (callId.indexOf(Converter.EXTERNAL_ERROR) == 0) {
            this.addToCurrentBlock(new AbortCommandNode(
                callId,
                this.calls.peek().getLine(),
                this.calls.peek().getPos()
                , null));

            this.currentBlock().setRecentOriginalText("ABORT");

            return;
        }

        if (callId.indexOf(Converter.EXTERNAL_NONDET) == 0) {
            return;
        }

        final ArrayList<CommandNode> assignCommands = new ArrayList<>();

        final ArrayList<VariableNode> parameters = new ArrayList<>();

        for (final String p : this.functionDeclarations.get(callId).getParams()) {
            parameters.add(new VariableNode("", 0, 0, p, callId, VariableNode.Type.PARAMTER));
        }

        Collections.reverse(parameters);

        for (final VariableNode vn : parameters) { //!parameters.isEmpty()) {
            //  final VariableNode parameter = parameters.pop();
            final NumericExpressionNode assignExp = this.popNumericExpression();
            final VariableNode assignVar =
                new VariableNode(
                    "",
                    0,
                    0,
                    "$stack" + this.idCounter++,
                    this.currentFunction,
                    VariableNode.Type.VARIABLE);
            this.addToCurrentBlock(new AssignCommandNode("", 0, 0, null, assignVar, assignExp));

            assignCommands.add(new PushCommandNode("", 0, 0, null, assignVar));

            /*   assignCommands.add(new AssignCommandNode(
                   assign.getText(),
                   assign.getLine(),
                   assign.getPos(),
                   null,
                   parameter,
                   assign)); */
        }

        this.addAllToCurrentBlock(assignCommands);

        final CommandNode callCmd =
            new CallCommandNode(
                node.toString(),
                0,
                0,
                null,
                new LabelNode(
                    callId,
                    LabelNode.Type.FUNCTION_BEGIN,
                    0), callId);


        this.addToCurrentBlock(callCmd);
        this.currentBlock().setRecentOriginalText("CALL " + node.toString());
    }


    @Override
    public void outAFunctionNumericItem(final AFunctionNumericItem node) {

        final String callId = this.calls.peek().getText();

        if (callId.indexOf(Converter.EXTERNAL_NONDET) == 0) {
            final String name = "?" + Converter.COEF_COUNTER++;
            //            final VariableNode ndtVar =
            //                new VariableNode(
            //                    name,
            //                    this.calls.peek().getLine(),
            //                    this.calls.peek().getPos(),
            //                    name,
            //                    this.currentFunction,
            //                    Type.VARIABLE);

            final VariableNode ndtValue =
                new VariableNode(
                    node.toString(),
                    this.calls.peek().getLine(),
                    this.calls.peek().getPos(),
                    null,
                    this.currentFunction,
                    Type.NONDET);
            //
            //            this.expressions.push(ndtVar);
            //
            //            this.addToCurrentBlock(new AssignCommandNode(callId, this.calls.peek().getLine(), this.calls
            //                .peek()
            //                .getPos(), "", ndtVar, ndtValue));
            //
            //            this.currentBlock().addVariable(ndtVar);

            this.expressions.push(ndtValue);

            this.currentBlock().addVariable(ndtValue);

        } else {
            if (this.functionDeclarations.get(callId).isVoid()) {
                throw new ConvertException(
                    this.calls.peek().getLine(),
                    this.calls.peek().getPos(),
                    "Can not evaluate void function: " + callId);
            }

            //final VariableNode returnVar = new VariableNode(callId, 0, 0, null, callId, VariableNode.Type.RETURN);

            final String var = callId + String.valueOf(this.callCounter++);

            final VariableNode returnVarSpec =
                new VariableNode(
                    var,
                    0,
                    0,
                    var,
                    this.currentFunction,
                    VariableNode.Type.VARIABLE);

            this.addToCurrentBlock(new PopCommandNode("", 0, 0, null, returnVarSpec));

            //  this.addToCurrentBlock(new AssignCommandNode("", 0, 0, null, returnVarSpec, returnVar));

            this.expressions.push(returnVarSpec);

            this.currentBlock().addVariable(returnVarSpec);
        }

        this.calls.pop();
    }

    @Override
    public void outACallSimpleStatement(final ACallSimpleStatement node) {
        this.calls.pop();
    }

    private void binaryNumericExp(final BinrayNumericExpressionNode.Type type) {
        final NumericExpressionNode expB = this.popNumericExpression();

        //        if (type == BinrayNumericExpressionNode.Type.DIV && expB.getPolyFraction().getDenumenator().isZero()) {
        //            throw new ConvertException(expB.getLine(), expB.getPos(), "Attempt to divide by zero: " + expB.getText());
        //        }

        final NumericExpressionNode expA = this.popNumericExpression();

        this.expressions.push(new BinrayNumericExpressionNode(
            expA.getText() + type.getSymbol() + expB.getText(),
            expA.getLine(),
            expA
            .getPos(), expA, expB, type));
    }

    @Override
    public void outAMultiplicationNumericFactor(final AMultiplicationNumericFactor node) {
        this.binaryNumericExp(BinrayNumericExpressionNode.Type.MUL);
        //        final NumericExpressionNode expB = this.expressions.pop();
        //        final NumericExpressionNode expA = this.expressions.pop();
        //
        //        this.expressions.push(new BinrayNumericExpressionNode(
        //            node.toString(),
        //            expA.getLine(),
        //            expA
        //            .getPos(), expA, expB, BinrayNumericExpressionNode.Type.MUL));
    }

    @Override
    public void outADivisionNumericFactor(final ADivisionNumericFactor node) {
        this.binaryNumericExp(BinrayNumericExpressionNode.Type.DIV);
        //        final NumericExpressionNode expB = this.expressions.pop();
        //        final NumericExpressionNode expA = this.expressions.pop();
        //
        //        this.expressions.push(new BinrayNumericExpressionNode(
        //            node.toString(),
        //            expA.getLine(),
        //            expA
        //            .getPos(), expA, expB, BinrayNumericExpressionNode.Type.DIV));
    }

    private static int COEF_COUNTER = 0;

    @Override
    public void outAModuloNumericFactor(final AModuloNumericFactor node) {
        final NumericExpressionNode expB = this.popNumericExpression();
        final NumericExpressionNode expA = this.popNumericExpression();

        final String varM = "M^" + Converter.COEF_COUNTER++;
        final VariableNode m = new VariableNode(varM, 0, 0, varM, this.currentFunction, Type.VARIABLE);
        final String varN = "N^" + Converter.COEF_COUNTER++;
        final VariableNode n = new VariableNode(varN, 0, 0, varN, this.currentFunction, Type.VARIABLE);

        final BooleanExpressionNode condM =
            new ComplexBooleanExpressionNode("", 0, 0, new BinaryBooleanExpressionNode(
                "",
                0,
                0,
                m,
                ConstantNumericExpressionNode.ZERO,
                BinaryBooleanExpressionNode.Type.GREATER_EQ), new BinaryBooleanExpressionNode(
                    "",
                    0,
                    0,
                    expB,
                    m,
                    BinaryBooleanExpressionNode.Type.GREATER), ComplexBooleanExpressionNode.Type.AND);



        final BooleanExpressionNode condN =
            new BinaryBooleanExpressionNode(
                "",
                0,
                0,
                n,
                ConstantNumericExpressionNode.ZERO,
                BinaryBooleanExpressionNode.Type.GREATER_EQ);

        final BooleanExpressionNode condA =
            new BinaryBooleanExpressionNode(
                "",
                0,
                0,
                expA,
                expB.times(n).add(m),
                BinaryBooleanExpressionNode.Type.EQUAL);

        this.addToCurrentBlock(new AssignCommandNode("", 0, 0, null, n, new VariableNode(
            "NDT",
            0,
            0,
            null,
            null,
            Type.NONDET)));
        this.addToCurrentBlock(new AssumeCommandNode("", 0, 0, null, new VariableNode(
            "NDT",
            0,
            0,
            null,
            null,
            Type.NONDET)));

        this.addToCurrentBlock(new AssignCommandNode("", 0, 0, null, m, expA.sub(n.times(expB))));
        //  this.addToCurrentBlock(new AssumeCommandNode("", 0, 0, null, condN));
        this.addToCurrentBlock(new AssumeCommandNode("", 0, 0, null, condM));
        this.addToCurrentBlock(new AssumeCommandNode("", 0, 0, null, condA));

        this.expressions.push(m);
    }

    @Override
    public void outAAddAssignment(final AAddAssignment node) {
        final NumericExpressionNode expC = this.popNumericExpression();

        final VariableNode expA = this.popVariable();

        final NumericExpressionNode expB =
            new BinrayNumericExpressionNode(
                expA.getText() + node.getPlus().getText() + expC.toString(),
                expA.getLine(),
                expA.getPos(),
                expA,
                expC,
                BinrayNumericExpressionNode.Type.ADD);

        this.validateNumericExpression(expB);

        this.assignments.push(new Triple<>(expA, expB, node.toString()));
    }

    @Override
    public void outASubAssignment(final ASubAssignment node) {
        final NumericExpressionNode expC = this.popNumericExpression();

        final VariableNode expA = this.popVariable();

        final NumericExpressionNode expB =
            new BinrayNumericExpressionNode(
                expA.getText() + node.getMinus().getText() + expC.toString(),
                expA.getLine(),
                expA.getPos(),
                expA,
                expC,
                BinrayNumericExpressionNode.Type.SUB);

        this.validateNumericExpression(expB);

        this.assignments.push(new Triple<>(expA, expB, node.toString()));
    }

    @Override
    public void outAIncAssignment(final AIncAssignment node) {
        final VariableNode expA = this.popVariable();

        final NumericExpressionNode expB =
            new BinrayNumericExpressionNode(
                expA.getText() + node.getDplus().getText(),
                expA.getLine(),
                expA.getPos(),
                expA,
                new ConstantNumericExpressionNode("", 0, 0, 1),
                BinrayNumericExpressionNode.Type.ADD);

        this.validateNumericExpression(expB);

        this.assignments.push(new Triple<>(expA, expB, node.toString()));
    }

    @Override
    public void outADecAssignment(final ADecAssignment node) {
        final VariableNode expA = this.popVariable();

        final NumericExpressionNode expB =
            new BinrayNumericExpressionNode(
                expA.getText() + node.getDminus().getText(),
                expA.getLine(),
                expA.getPos(),
                expA,
                new ConstantNumericExpressionNode("", 0, 0, 1),
                BinrayNumericExpressionNode.Type.SUB);
        this.validateNumericExpression(expB);

        this.assignments.push(new Triple<>(expA, expB, node.toString()));
    }


    @Override
    public void outASimpleAssignment(final ASimpleAssignment node) {
        final NumericExpressionNode expB = this.popNumericExpression();
        this.validateNumericExpression(expB);

        final VariableNode expA = this.popVariable();

        this.assignments.push(new Triple<>(expA, expB, node.toString()));
    }

    @Override
    public void outAAssignSimpleStatement(final AAssignSimpleStatement node) {
        final Triple pair = this.assignments.pop();

        final VariableNode expA = (VariableNode) pair.x;
        final NumericExpressionNode expB = (NumericExpressionNode) pair.y;


        this.addToCurrentBlock(
            new AssignCommandNode(
                node.toString(),
                expA.getLine(),
                expA.getPos(),
                null,
                expA,
                expB));

        this.currentBlock().setRecentOriginalText(node.toString());
    }

    @Override
    public void outAAdditionNumericExp(final AAdditionNumericExp node) {
        this.binaryNumericExp(BinrayNumericExpressionNode.Type.ADD);
        //        final NumericExpressionNode expB = this.expressions.pop();
        //        final NumericExpressionNode expA = this.expressions.pop();
        //
        //        this.expressions.push(new BinrayNumericExpressionNode(
        //            node.toString(),
        //            expA.getLine(),
        //            expA
        //            .getPos(), expA, expB, BinrayNumericExpressionNode.Type.ADD));
    }

    @Override
    public void outASubtractionNumericExp(final ASubtractionNumericExp node) {
        this.binaryNumericExp(BinrayNumericExpressionNode.Type.SUB);
        //        final NumericExpressionNode expB = this.expressions.pop();
        //        final NumericExpressionNode expA = this.expressions.pop();
        //
        //        this.expressions.push(new BinrayNumericExpressionNode(
        //            node.toString(),
        //            expA.getLine(),
        //            expA
        //            .getPos(), expA, expB, BinrayNumericExpressionNode.Type.SUB));
    }

    @Override
    public void inAConstantInt(final AConstantInt node) {
        this.expressions.push(new ConstantNumericExpressionNode(node.toString(), node.getNum().getLine(), node
            .getNum()
            .getLine(), Integer
            .parseInt(node
                .getNum()
                .getText()
                .trim())));

        //        final boolean isNegative = node.getMinus() != null;
        //        final int line = isNegative ? node.getMinus().getLine() : node.getNum().getLine();
        //        final int pos = isNegative ? node.getMinus().getPos() : node.getNum().getPos();
        //        this.expressions.push(new ConstantNumericExpressionNode(node.toString(), line, pos, Integer
        //            .parseInt((isNegative ? "-" : "") + node.getNum().getText().trim())));
    }

    @Override
    public void inAVariableId(final AVariableId node) {
        final String id = node.getId().getText();
        VariableNode var = null;

        if (this.isGlobal(id)) {
            var =
                new VariableNode(
                    node.toString(),
                    node.getId().getLine(),
                    node.getId().getPos(),
                    id,
                    null,
                    VariableNode.Type.GLOBAL);
        } else {
            var =
                new VariableNode(
                    node.toString(),
                    node.getId().getLine(),
                    node.getId().getPos(),
                    id,
                    this.currentFunction,
                    VariableNode.Type.VARIABLE);
        }

        this.expressions.push(var);
    }

    private boolean isGlobal(final String id) {
        return this.globals.contains(id);
    }

    @Override
    public void outAReturnSimpleStatement(final AReturnSimpleStatement node) {

        if (node.getNumericExp() != null) {

            if (this.functionDeclarations.get(this.currentFunction).isVoid()) {
                throw new ConvertException(
                    node.getReturn().getLine(),
                    node.getReturn().getPos(),
                    "Void function can not return value: " + this.currentFunction);
            }


            final NumericExpressionNode exp = this.popNumericExpression();
            this.validateNumericExpression(exp);

            final VariableNode assignVar =
                new VariableNode(
                    "",
                    0,
                    0,
                    "$stack" + this.idCounter++,
                    this.currentFunction,
                    VariableNode.Type.VARIABLE);
            this.addToCurrentBlock(new AssignCommandNode("", 0, 0, null, assignVar, exp));

            this.addToCurrentBlock(new PushCommandNode(node.toString(), node.getReturn().getLine(), node
                .getReturn()
                .getPos(), null, assignVar));

            /*  this.addToCurrentBlock(
                  new AssignCommandNode(node.toString(), node.getReturn().getLine(), node
                      .getReturn()
                      .getPos(), null, new VariableNode(
                          node.toString(),
                          node.getReturn().getLine(),
                          node
                          .getReturn()
                          .getPos(), null, this.currentFunction, VariableNode.Type.RETURN), exp)); */
        } else {
            if (!this.functionDeclarations.get(this.currentFunction).isVoid()) {
                throw new ConvertException(
                    node.getReturn().getLine(),
                    node.getReturn().getPos(),
                    "Function must return value: " + this.currentFunction);
            }
        }


        this.addToCurrentBlock(
            new BranchCommandNode(
                node.toString(),
                node.getReturn().getLine(),
                node
                .getReturn()
                .getPos(), null, new LabelNode(this.currentFunction, LabelNode.Type.FUNCTION_END, 0)));

        this.currentBlock().setRecentOriginalText(node.toString());

        this.currentBlock().setReturnValueStatement(true);

    }


    @Override
    public void inABlock(final ABlock node) {
        this.inBlock(LabelNode.Type.NONE, "");
    }

    @Override
    public void outABlock(final ABlock node) {
        //  this.extractCurrentToFather();
    }


    @Override
    public void inABlockWithElse(final ABlockWithElse node) {
        this.inBlock(LabelNode.Type.NONE, "");
    }

    @Override
    public void outABlockWithElse(final ABlockWithElse node) {
        //this.extractCurrentToFather();
    }

    private void inBlock(final LabelNode.Type type, final String id) {
        this.commandBlocks.push(new Block(this.currentBlock(), type, id));
    }

    @Override
    public void inAAssertionSimpleStatement(final AAssertionSimpleStatement node) {
        this.inBlock(LabelNode.Type.NONE, null);
    }

    @Override
    public void outAAssertionSimpleStatement(final AAssertionSimpleStatement node) {

        this.addToCurrentBlock(
            new ConditionalBranchCommandNode(
                node.toString(),
                node.getAssert().getLine(),
                node
                .getAssert()
                .getPos(),
                null, new LabelNode(
                    this.currentFunction,
                    LabelNode.Type.IF_BREAK,
                    this
                    .currentBlock()
                    .getNumber()), this.expressions.pop()));

        this.currentBlock().setRecentOriginalText(node.toString());

        this.addToCurrentBlock(
            new AbortCommandNode(node.toString(), node.getAssert().getLine(), node
                .getAssert()
                .getPos(), null));

        this.currentBlock().setRecentOriginalText("Abort");

        this.setNextLabel(new LabelNode(
            this.currentFunction,
            LabelNode.Type.IF_BREAK,
            this.currentBlock().getNumber()));

        this.extractCurrentToFather();
    }


    @Override
    public void inAIfSimpleStatement(final AIfSimpleStatement node) {
        this.inBlock(LabelNode.Type.NONE, null);
    }

    @Override
    public void outAIfSimpleStatement(final AIfSimpleStatement node) {
        final ArrayList<CommandNode> commands = this.extractCurrentBlock();

        this.addToCurrentBlock(
            new ConditionalBranchCommandNode(
                node.getIf().toString() + " " + node.getCondition().toString(),
                node.getIf().getLine(),
                node.getIf().getPos(),
                null, new LabelNode(
                    this.currentFunction,
                    LabelNode.Type.IF_BREAK,
                    this.currentBlock().getNumber()),
                    new NegatedBooleanExpressionNode(node.getIf().toString() + " " + node.getCondition().toString(), node
                        .getIf()
                        .getLine(), node.getIf().getPos(), this.expressions.pop())));

        this.currentBlock().setRecentOriginalText(node.getIf().toString() + " " + node.getCondition().toString());

        this.addAllToCurrentBlock(commands);

        this.setNextLabel(new LabelNode(
            this.currentFunction,
            LabelNode.Type.IF_BREAK,
            this.currentBlock().getNumber()));

        this.extractCurrentToFather();
    }

    private void outIfElse(final int line, final int pos, final String conditionText) {
        boolean returnStatement = this.currentBlock().hasReturnValueStatement();
        final ArrayList<CommandNode> elseBlock = this.extractCurrentBlock();

        returnStatement = returnStatement && this.currentBlock().hasReturnValueStatement();
        final ArrayList<CommandNode> ifBlock = this.extractCurrentBlock();

        try {
            this.setNextLabel(new LabelNode(this.currentFunction, LabelNode.Type.IF_CONDITION, this
                .currentBlock()
                .getNumber()));
        } catch (final Exception e) {
            final int k = 0; //debug
        }

        this.addToCurrentBlock(
            new ConditionalBranchCommandNode(
                "if " + conditionText, line, pos,
                null, new LabelNode(
                    this.currentFunction,
                    LabelNode.Type.ELSE_BLOCK,
                    this.currentBlock().getNumber()),
                    this.expressions.pop().negate()));

        this.currentBlock().setRecentOriginalText("if " + conditionText);

        this.addAllToCurrentBlock(ifBlock);

        this.addToCurrentBlock(
            new BranchCommandNode(
                "if " + conditionText, line, pos,
                null, new LabelNode(
                    this.currentFunction,
                    LabelNode.Type.IF_BREAK,
                    this.currentBlock().getNumber())));

        this.setNextLabel(new LabelNode(
            this.currentFunction,
            LabelNode.Type.ELSE_BLOCK,
            this
            .currentBlock()
            .getNumber()));

        this.addAllToCurrentBlock(elseBlock);

        this.setNextLabel(new LabelNode(
            this.currentFunction,
            LabelNode.Type.IF_BREAK,
            this.currentBlock().getNumber()));

        this.setCurrentRetunStatememt(returnStatement);

        this.extractCurrentToFather();
    }

    @Override
    public void inAIfElseStatement(final AIfElseStatement node) {
        this.inBlock(LabelNode.Type.NONE, null);
    }

    @Override
    public void outAIfElseStatement(final AIfElseStatement node) {
        this.outIfElse(node.getIf().getLine(), node.getIf().getPos(), node.getCondition().toString());
    }

    @Override
    public void inAIfElseStatementWithElse(final AIfElseStatementWithElse node) {
        this.inBlock(LabelNode.Type.NONE, null);
    }

    @Override
    public void outAIfElseStatementWithElse(final AIfElseStatementWithElse node) {
        this.outIfElse(node.getIf().getLine(), node.getIf().getPos(), node.getCondition().toString());
    }

    private void outWhile(final int line, final int pos, final String conditionText) {
        final ArrayList<CommandNode> commands = this.extractCurrentBlock();

        this.addToCurrentBlock(
            new ConditionalBranchCommandNode(
                "while " + conditionText,
                line,
                pos,
                null, new LabelNode(
                    this.currentFunction,
                    LabelNode.Type.WHILE_BREAK,
                    this.currentBlock().getNumber()),
                    new NegatedBooleanExpressionNode("", 0, 0, this.expressions.pop())));

        this.currentBlock().setRecentOriginalText("while " + conditionText);

        this.addAllToCurrentBlock(commands);

        this.addToCurrentBlock(
            new BranchCommandNode(
                "while " + conditionText, line, pos,
                null,
                new LabelNode(
                    this.currentFunction,
                    LabelNode.Type.WHILE_CONDITION,
                    this.currentBlock().getNumber())));

        this
        .setNextLabel(new LabelNode(
            this.currentFunction,
            LabelNode.Type.WHILE_BREAK,
            this
            .currentBlock()
            .getNumber()));

        this.extractCurrentToFather();
    }

    @Override
    public void inAWhileStatement(final AWhileStatement node) {
        this.inBlock(LabelNode.Type.WHILE_CONDITION, this.currentFunction);
    }

    @Override
    public void outAWhileStatement(final AWhileStatement node) {
        this.outWhile(node.getWhile().getLine(), node.getWhile().getPos(), node.getCondition().toString());
    }

    @Override
    public void inAWhileStatementWithElse(final AWhileStatementWithElse node) {
        this.inBlock(LabelNode.Type.WHILE_CONDITION, this.currentFunction);
    }

    @Override
    public void outAWhileStatementWithElse(final AWhileStatementWithElse node) {
        this.outWhile(node.getWhile().getLine(), node.getWhile().getPos(), node.getCondition().toString());
    }

    /*
    @Override
    public void outAAssignsListSingle(AAssignSimpleStatement node) {
        final NumericExpressionNode expB = this.expressions.pop();
        validateNumericExpression(expB);

        final VariableNode expA = this.popVariable();
        this.currentFunctionVariables.add(expA);

        this.addToCurrentBlock(new AssignCommandNode(
            node.toString(),
            expA.getLine(),
            expA.getPos(),
            null,
            expA,
            expB));

        this.currentBlock().setRecentOriginalText(node.toString());
    }*/

    @Override
    public void inAForStatement(final AForStatement node) {
        this.commandBlocks.push(new Block(this.currentBlock(), LabelNode.Type.NONE, null));
    }

    @Override
    public void caseAForStatement(final AForStatement node) {
        this.inAForStatement(node);
        if (node.getLabel() != null) {
            node.getLabel().apply(this);
        }
        if (node.getFor() != null) {
            node.getFor().apply(this);
        }

        this.addToCurrentBlock(
            new NoOperationCommandNode(node.getFor().getText(), node.getFor().getLine(), node
                .getFor()
                .getPos(), null));

        this.currentBlock().setRecentOriginalText(node.getFor().getText());

        if (node.getParL() != null) {
            node.getParL().apply(this);
        }
        {
            node.getInit().apply(this);
        }


        while (!this.assignments.isEmpty()) {
            final Triple<VariableNode, NumericExpressionNode, String> triple = this.assignments.pop();

            final VariableNode expA = triple.x;
            final NumericExpressionNode expB = triple.y;
            final String text = triple.z;

            this.addToCurrentBlock(
                new AssignCommandNode(
                    text,
                    expA.getLine(),
                    expA.getPos(),
                    null, expA, expB));

            this.currentBlock().setRecentOriginalText(text);
        }

        if (node.getDelimiter1() != null) {
            node.getDelimiter1().apply(this);
        }

        if (node.getCond() != null) {
            node.getCond().apply(this);
        }

        this.setNextLabel(new LabelNode(
            this.currentFunction,
            LabelNode.Type.FOR_CONDITION,
            this.currentBlock().getNumber()));


        if (!this.expressions.isEmpty()) {
            this.addToCurrentBlock(
                new ConditionalBranchCommandNode(
                    null,
                    node.getFor().getLine(),
                    node.getFor().getPos(),
                    null,
                    new LabelNode(this.currentFunction,
                        LabelNode.Type.FOR_BREAK,
                        this
                        .currentBlock()
                        .getNumber()),
                        new NegatedBooleanExpressionNode("", 0, 0, this.expressions.pop())));

            // this.currentBlock().setRecentOriginalText("FOR COND");
        }

        if (node.getDelimiter2() != null) {
            node.getDelimiter2().apply(this);
        }

        {
            node.getStep().apply(this);
        }

        final ArrayList<CommandNode> step = new ArrayList<>();

        while (!this.assignments.isEmpty()) {
            final Triple<VariableNode, NumericExpressionNode, String> triple = this.assignments.pop();

            final VariableNode expA = triple.x;
            final NumericExpressionNode expB = triple.y;
            final String text = triple.z;

            step.add(new AssignCommandNode(
                text,
                expA.getLine(),
                expA.getPos(), null, expA, expB));
        }

        if (node.getParR() != null) {
            node.getParR().apply(this);
        }
        if (node.getBlock() != null) {
            node.getBlock().apply(this);
        }

        this.addAllToCurrentBlock(this.extractCurrentBlock());

        for (final CommandNode cmd : step) {
            this.addToCurrentBlock(cmd);
            this.currentBlock().setRecentOriginalText(cmd.getText());
        }

        this.addToCurrentBlock(
            new BranchCommandNode(
                null,
                node.getFor().getLine(),
                node.getFor().getPos(),
                null,
                new LabelNode(this.currentFunction, LabelNode.Type.FOR_CONDITION, this.currentBlock().getNumber())));

        this.setNextLabel(new LabelNode(
            this.currentFunction,
            LabelNode.Type.FOR_BREAK,
            this.currentBlock().getNumber()));

        this.outAForStatement(node);
    }

    /**
     * @param node - numeric expression node
     */
    private void validateNumericExpression(final NumericExpressionNode node) {
        //        if (node instanceof VariableNode && ((VariableNode) node).isNonDet()) {
        //            return;
        //        }

        for (final String varName : node.getVariablesId()) {
            if (!this.globals.contains(varName) && !this.currentBlock().variableExists(varName)) {
                throw new ConvertException(node.getLine(), node.getPos(), "Use of an undefined variable: " + varName);
            }
        }
    }

    private void setNextLabel(final LabelNode label) {
        this.addToCurrentBlock(new NoOperationCommandNode(label.getText(), label.getLine(), label.getPos(), label
            .toString()));
    }

    private static String ALLOWED_EXTERNAL_PREFIX = "__VERIFIER_";
    private static String EXTERNAL_ERROR = Converter.ALLOWED_EXTERNAL_PREFIX + "error";
    private static String EXTERNAL_NONDET = Converter.ALLOWED_EXTERNAL_PREFIX + "nondet";
    private static String MAIN_FUNCTION = "main";
}
