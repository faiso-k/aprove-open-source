package aprove.verification.complexity.LowerBounds.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.oldframework.BasicStructures.*;

public abstract class TypedTrs extends Trs {

    private TrsTypes types;

    public TypedTrs(Set<Rule> rules, TrsTypes types, boolean innermost) {
        super(rules, innermost);
        this.types = types;
    }

    public TrsTypes getTypes() {
        return this.types;
    }

    public Set<FunctionSymbol> getRecursiveConstructors(Type t) {
        Set<FunctionSymbol> res = new LinkedHashSet<>();
        for (FunctionSymbol c : this.constructors) {
            FunctionSymbolSimpleType type = this.types.get(c);
            if (type.getReturnType().equals(t) && type.isRecursive()) {
                res.add(c);
            }
        }
        return res;
    }

    public Set<FunctionSymbol> getNonRecursiveConstructors(Type t) {
        Set<FunctionSymbol> res = new LinkedHashSet<>();
        for (FunctionSymbol c : this.constructors) {
            FunctionSymbolSimpleType type = this.types.get(c);
            if (type.getReturnType().equals(t) && !type.isRecursive()) {
                res.add(c);
            }
        }
        return res;
    }

    public List<Type> getArgumentTypes(FunctionSymbol symbol) {
        return this.types.getArgumentTypes(symbol);
    }

    public FunctionSymbolSimpleType getType(FunctionSymbol symbol) {
        return this.types.get(symbol);
    }

    public boolean hasRecursiveConstructor(Type type) {
        return !this.getRecursiveConstructors(type).isEmpty();
    }

    @Override
    public String export(Export_Util eu) {
        String res = super.export(eu);
        res += eu.linebreak();
        res += eu.escape("Types:");
        res += eu.linebreak();
        res += this.types.export(eu);
        return res;
    }
}
