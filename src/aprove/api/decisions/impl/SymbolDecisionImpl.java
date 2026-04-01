package aprove.api.decisions.impl;

import java.util.*;
import java.util.stream.*;

import aprove.api.decisions.*;
import aprove.api.decisions.results.*;
import aprove.verification.oldframework.BasicStructures.*;

public class SymbolDecisionImpl implements SymbolDecision {

    public static SymbolDecisionImpl createWithoutModing(Set<FunctionSymbol> functionSymbols) {
        return new SymbolDecisionImpl(createSetOfNames(functionSymbols), Optional.empty());
    }

    public static SymbolDecisionImpl createWithModing(Set<FunctionSymbol> functionSymbols) {
        return new SymbolDecisionImpl(createSetOfNames(functionSymbols),
                                      Optional.of(new SymbolModingDecisionImpl(functionSymbols)));
    }

    private static List<String> createSetOfNames(Set<FunctionSymbol> symbols) {
        return symbols.stream().map(FunctionSymbol::getName).collect(Collectors.toList());
    }

    private final List<String> symbols;
    private final Optional<SymbolModingDecisionImpl> symbolModingDecision;

    public SymbolDecisionImpl(List<String> symbols, Optional<SymbolModingDecisionImpl> symbolModingDecision) {
        this.symbols = symbols;
        this.symbolModingDecision = symbolModingDecision;
    }

    @Override
    public List<String> getSymbols() {
        return symbols;
    }

    public Optional<SymbolModingDecisionImpl> getModingDecision() {
        return symbolModingDecision;
    }

    public SymbolDecisionResult makeDecision(String symbol) throws InvalidDecisionException {
        Objects.requireNonNull(symbol);
        if (symbols.contains(symbol)) {
            return new SymbolDecisionResult(this, symbol);
        } else {
            throw new InvalidDecisionException("unknown symbol");
        }
    }
}
