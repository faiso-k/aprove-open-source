package aprove.input.Programs.impact;

import java.util.*;

import aprove.input.Generated.impact.analysis.*;
import aprove.input.Generated.impact.node.*;
import aprove.input.Programs.impact.Program.*;
import aprove.input.Utility.*;

/**
 * Initial pass, collect function declarations and global variables declarations
 *
 * @author marinag
 *
 */
public class Pass extends DepthFirstAdapter {
    private final ParseErrors parseErrors;
    private String currentFunction;
    private boolean isCurrentVoid;

    private final HashMap<String, FunctionDeclaration> functionDeclarations;
    private ArrayList<String> currentFunctionParameters;
    private HashSet<String> labels = null;
    private final HashSet<String> globals = new HashSet<>();

    public Pass() {
        this.parseErrors = new ParseErrors();
        this.functionDeclarations = new HashMap<>();
    }

    @Override
    public void inAFunctionId(final AFunctionId node) {
        this.currentFunction = node.getId().getText();
        this.currentFunctionParameters = new ArrayList<>();
    }

    @Override
    public void inAFunctionVariableId(final AFunctionVariableId node) {
        final String name = node.getId().getText();

        if (this.currentFunctionParameters.contains(name)) {
            throw new ConvertException(node.getId().getLine(), node.getId().getPos(), "Redifinition of parameters: "
                + name
                + " at function: "
                + this.currentFunction);
        }

        this.currentFunctionParameters.add(name);
    }

    @Override
    public void outAVoidReturnType(final AVoidReturnType node) {
        this.isCurrentVoid = true;
    }

    @Override
    public void outAValueReturnType(final AValueReturnType node) {
        this.isCurrentVoid = false;
    }

    @Override
    public void outALabel(final ALabel node) {
        this.labels.add(node.getId().getText());
    }

    @Override
    public void inAFunctionDefinition(final AFunctionDefinition node) {
        this.labels = new HashSet<>();
    }

    @Override
    public void outAFunctionDefinition(final AFunctionDefinition node) {
        if (this.functionDeclarations.containsKey(this.currentFunction)) {
            throw new ConvertException(0, 0, "Redifinition of function " + this.currentFunction);
        }

        this.functionDeclarations.put(this.currentFunction, new FunctionDeclaration(
            this.currentFunction,
            this.isCurrentVoid,
            this.currentFunctionParameters,
            this.labels));
        this.currentFunction = null;
        this.currentFunctionParameters = null;
        this.labels = null;
    }

    @Override
    public void outAFunctionDeclaration(final AFunctionDeclaration node) {
        this.currentFunction = null;
    }

    @Override
    public void outAExternalDeclaration(final AExternalDeclaration node) {
        this.currentFunction = null;
    }

    /**
     * @return functions declarations
     */
    public HashMap<String, FunctionDeclaration> getFunctionDeclarations() {
        return this.functionDeclarations;
    }

    @Override
    public void inAVariableId(final AVariableId node) {
        if (this.currentFunction == null) {
            this.globals.add(node.getId().getText());
        }
    }

    /**
     * @return global variables names
     */
    public HashSet<String> getGlobals() {
        return this.globals;
    }

    /**
     * @return ParseErrors
     */
    public ParseErrors getErrors() {
        return this.parseErrors;
    }
}
