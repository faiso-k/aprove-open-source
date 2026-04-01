package aprove.input.Programs.impact.Program;

import java.util.*;

import aprove.input.Programs.impact.*;
import aprove.input.Programs.impact.GTP.nodes.*;
import aprove.input.Programs.impact.GTP.nodes.LabelNode.*;

public class Block {

    private final int number;
    private final ArrayList<CommandNode> commands;
    private final HashMap<String, VariableNode> variables;
    private final LabelNode.Type type;
    private final String id;
    private boolean returnValueStatement;
    private boolean isOpen = true;
    private int depth;

    public Block(final Block father, final LabelNode.Type type, final String id) {
        this.number = Block.COUNTER++;
        this.id = id;
        this.type = type;
        this.commands = new ArrayList<>();
        this.variables = new HashMap<>();

        if (father != null) {
            this.variables.putAll(father.variables);
            this.depth = father.depth + 1;
        } else {
            this.depth = 0;
        }

        this.returnValueStatement = false;

        if (!this.type.equals(Type.NONE)) {
            this.addCommand(new NoOperationCommandNode("", 0, 0, new LabelNode(this.id, this.type, this.number)
                .toString()));
        }
    }

    public int getNumber() {
        return this.number;
    }

    public boolean hasReturnValueStatement() {
        return this.returnValueStatement;
    }

    public void setReturnValueStatement(final boolean value) {
        this.returnValueStatement = value;
    }

    private HashSet<String> getVariables() {
        final HashSet<String> result = new HashSet<>();

        for (final VariableNode var : this.variables.values()) {
            result.add(var.toString());
        }

        return result;
    }

    public void addCommand(final CommandNode command) {
        this.commands.add(command);
        command.setAvaliableVariables(this.getVariables());
    }


    public void addCommand(final int index, final CommandNode command) {
        this.commands.add(index, command);
        command.setAvaliableVariables(this.getVariables());
    }

    public void addAllCommands(final ArrayList<CommandNode> commands) {
        this.commands.addAll(commands);

        final HashSet<String> vars = this.getVariables();

        for (final CommandNode command : commands) {
            command.setAvaliableVariables(vars);
        }
    }

    public ArrayList<CommandNode> getCommands() {
        return this.commands;
    }

    public void addVariable(final VariableNode var) {
        final String varName = var.getText();

        if (this.variableExists(varName)) {
            throw new ConvertException(var.getLine(), var.getPos(), "Redifinition of variable: " + varName);
        }

        this.variables.put(varName.trim(), var);
    }


    public boolean variableExists(final String name) {
        return this.variables.containsKey(name);
    }

    /*
    public Set<String> getVariables() {
        return this.variables;
    }*/

    public void setRecentOriginalText(final String text) {
        this.commands.get(this.commands.size() - 1).setOriginalText(text);
    }

    private static int COUNTER = 0;

    public void close() {
        this.isOpen = false;
    }
}
