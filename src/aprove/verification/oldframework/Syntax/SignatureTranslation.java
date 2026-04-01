package aprove.verification.oldframework.Syntax;

import java.util.*;

/**
 * basically a map from function symbols to function symbols. Ensures bijectivity
 * @author Christian Kaeunicke
 */

public class SignatureTranslation extends LinkedHashMap<SyntacticFunctionSymbol, SyntacticFunctionSymbol> {
    public <S extends SyntacticFunctionSymbol> S translate(S sym) {
    // the next line assumes, that symbols only get translated into symbols of the same
    // class. If a class cast exception occures here, make sure that you really want to
    // have a signature translation that changes a symbols class.
    return (S) this.get(sym);
    };

    public <S extends SyntacticFunctionSymbol> Set<S> translate(Set<S> symbols) {
    Set<S> forReturn = new LinkedHashSet<S>();

    for (S current : symbols) {
        S temp = this.translate(current);
        if (temp != null) {
            forReturn.add(temp);
        }
    };

    return forReturn;
    };

    @Override
    public SyntacticFunctionSymbol put(SyntacticFunctionSymbol sym, SyntacticFunctionSymbol value) throws BijectivityViolation {
    if (this.containsValue(value)) {
        // value may already be in the set of values if it's the value for sym.
        if (this.containsKey(sym)) {
        if (this.get(sym).equals(value)) {
            return value;
        }
        }

        // if it's some other key's value, it's an error
        throw new BijectivityViolation("Symbol " + value.getName() + " is already in the set of values.\n");
    } else {
        return super.put(sym, value);
    }
    };

    /**
     * NOT implemented yet - throws a RuntimeException
     */
    public SyntacticFunctionSymbol putAllFS(final Map<SyntacticFunctionSymbol, SyntacticFunctionSymbol> map) {
    // If anyone plans to use this method she / he should enure the bijectivity criterion
    throw new RuntimeException("please implement SignatureTranslation.putAll() before using it!\n");
    };

    public SignatureTranslation reverse() {
    SignatureTranslation forReturn = new SignatureTranslation();

    for (Map.Entry<SyntacticFunctionSymbol, SyntacticFunctionSymbol> e : this.entrySet()) {
        forReturn.put(e.getValue(), e.getKey());
    };

    return forReturn;
    };

    @Override
    public String toString() {
    StringBuffer forReturn = new StringBuffer();

    boolean first = true;

    for (Map.Entry<SyntacticFunctionSymbol, SyntacticFunctionSymbol> e : this.entrySet()) {
        if (! first) {
            forReturn.append(",");
        }
        first = false;
        forReturn.append(e.getKey().getName() + "/" + e.getKey().getArity() + "->" +
                 e.getValue().getName() + "/" + e.getValue().getArity());
    };

    return forReturn.toString();
    };
};
