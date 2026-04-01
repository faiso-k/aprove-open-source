package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class Model {
    private final ImmutableMap<Symbol<?>, FunctionDefinition> definitions;

    public Model(ImmutableMap<Symbol<?>, FunctionDefinition> definitions) {
        this.definitions = definitions;
    }

    /**
     * This method is practically a shorthand for
     * Model.getDeclarations().get(symbol).getBody()
     * @author Hermann Walth
     * @param symbol The symbol to look up
     * @return The SMT expression defined for the symbol.
     */
    public SMTExpression<?> get(Symbol<?> symbol) {
        FunctionDefinition defn = this.definitions.get(symbol);
        if (defn == null) {
            return null;
        } else {
            return defn.getBody();
        }
    }

    public ImmutableMap<Symbol<?>, FunctionDefinition> getDeclarations() {
        return this.definitions;
    }

    @Override
    public String toString() {
        return this.definitions.values().toString();
    }
}
