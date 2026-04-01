package aprove.verification.oldframework.SMT.Utils;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;

public class VariableScope {

    private final ArrayDeque<LinkedHashMap<String, Symbol0<?>>> scopes = new ArrayDeque<>();

    public VariableScope() {
        this.pushScope();
    }

    public void pushScope() {
        this.scopes.push(new LinkedHashMap<String, Symbol0<?>>());
    }

    public void popScope() {
        this.scopes.pop();
    }

    public Symbol0<SInt> intVar(String name) {
        return this.var(name, SInt.representative);
    }

    public Symbol0<SBool> boolVar(String name) {
        return this.var(name, SBool.representative);
    }

    private <T extends Sort> Symbol0<T> var(String name, T representative) {
        assert !this.scopes.isEmpty();
        for (LinkedHashMap<String, Symbol0<?>> scope : this.scopes) {
            Symbol0<?> sym = scope.get(name);
            if (sym == null) {
                continue;
            }
            assert representative.equals(sym.getReturnSort());
            return (Symbol0<T>) sym;
        }
        LinkedHashMap<String, Symbol0<?>> top = this.scopes.peek();
        Symbol0<T> v = (Symbol0<T>) representative.createVariable();
        top.put(name, v);
        return v;
    }

    @Override
    public String toString() {
        StringBuilder rv = new StringBuilder();
        for (LinkedHashMap<String, Symbol0<?>> scope : this.scopes) {
            boolean first = true;
            for (Entry<String, Symbol0<?>> e : scope.entrySet()) {
                if (first) {
                    first = false;
                } else {
                    rv.append(", ");
                }
                rv.append(e.getKey());
            }
            rv.append('\n');
        }
        return rv.toString();
    }
}
