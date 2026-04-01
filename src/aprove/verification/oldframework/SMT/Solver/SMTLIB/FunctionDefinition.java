package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public class FunctionDefinition {

    private final ImmutableArrayList<Symbol0<?>> arguments;

    private final SMTExpression<?> body;

    private final Symbol<?> definedSymbol;

    public FunctionDefinition(Symbol<?> definedSymbol, ImmutableArrayList<Symbol0<?>> arguments, SMTExpression<?> body) {
        assert definedSymbol != null;
        assert arguments != null;
        assert body != null;
        assert arguments.size() == definedSymbol.getArgumentSorts().length;

        this.definedSymbol = definedSymbol;
        this.arguments = arguments;
        this.body = body;
    }

    public ImmutableArrayList<Symbol0<?>> getArguments() {
        return this.arguments;
    }

    public SMTExpression<?> getBody() {
        return this.body;
    }

    public Symbol<?> getDefinedSymbol() {
        return this.definedSymbol;
    }

    public FunctionDefinition substitute(Symbol0<?> oldVar, Symbol0<SInt> newVar) {
        if (newVar.equals(oldVar)) {
            return this;
        }
        ArrayList<Symbol0<?>> newArgs = new ArrayList<>(this.arguments);
        while (newArgs.contains(oldVar)) {
            newArgs.set(newArgs.indexOf(oldVar), newVar);
        }
        SMTExpression<?> newBody = this.body.accept(new SubstitutingExpressionVisitor(oldVar, newVar));
        return new FunctionDefinition(this.definedSymbol, ImmutableCreator.create(newArgs), newBody);
    }

    @Override
    public String toString() {
        return String.format("(define-fun %s %s)", this.definedSymbol, this.body);
    }
}
