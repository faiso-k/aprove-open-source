package aprove.api.decisions.impl;

import java.util.*;

import aprove.api.decisions.*;
import aprove.api.decisions.results.*;
import aprove.verification.oldframework.BasicStructures.*;

public class SymbolModingDecisionImpl implements SymbolModingDecision {

    private final Set<FunctionSymbol> functionSymbols;

    public SymbolModingDecisionImpl(Set<FunctionSymbol> functionSymbols) {
        this.functionSymbols = functionSymbols;
    }

    @Override
    public int getArity(String symbol) {
        Objects.requireNonNull(symbol);
        return functionSymbols.stream().filter(s -> s.getName().equals(symbol)).findFirst().get().getArity();
    }

    public SymbolModingDecisionResult makeDecision(String symbol,
                                                   List<Boolean> moding) throws InvalidDecisionException {
        Objects.requireNonNull(symbol);
        Objects.requireNonNull(moding);
        Optional<FunctionSymbol> functionSymbol = functionSymbols.stream()
                                                                 .filter(s -> s.getName().equals(symbol))
                                                                 .findFirst();
        if (functionSymbol.isPresent()) {
            int expectedSize = functionSymbol.get().getArity();
            if (moding.size() == expectedSize) {
                return new SymbolModingDecisionResult(this, moding);
            } else {
                throw new InvalidDecisionException("invalid moding: expected list of " + expectedSize + " booleans");
            }
        } else {
            throw new InvalidDecisionException("unknown symbol");
        }
    }
}
