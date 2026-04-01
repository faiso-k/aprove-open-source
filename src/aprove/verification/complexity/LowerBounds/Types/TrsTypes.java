package aprove.verification.complexity.LowerBounds.Types;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class TrsTypes implements Iterable<Type>, Exportable {

    private Map<FunctionSymbol, FunctionSymbolSimpleType> types = new LinkedHashMap<>();

    public void declare(FunctionSymbol symbol, FunctionSymbolSimpleType type) {
        assert !this.types.containsKey(symbol) || this.types.get(symbol).equals(type);
        this.types.put(symbol, type);
    }

    public Type getReturnType(FunctionSymbol symbol) {
        return this.get(symbol).getReturnType();
    }

    public List<Type> getArgumentTypes(FunctionSymbol symbol) {
        return this.get(symbol).getArgumentTypes();
    }

    public Set<Type> getTypes() {
        Set<Type> res = new LinkedHashSet<>();
        for (FunctionSymbolSimpleType functionType : this.types.values()) {
            res.add(functionType.getReturnType());
            res.addAll(functionType.getArgumentTypes());
        }
        return res;
    }

    public FunctionSymbolSimpleType get(FunctionSymbol c) {
        if (c.getArity() == 0 && PFHelper.isInt(TRSTerm.createFunctionApplication(c))) {
            return FunctionSymbolSimpleType.Nats;
        } else if (c.equals(PFHelper.ADD) || c.equals(PFHelper.MUL)) {
            return new FunctionSymbolSimpleType(Type.Nats, Type.Nats, Type.Nats);
        } else if (c.equals(PFHelper.EQ) || c.equals(PFHelper.GE)) {
            return new FunctionSymbolSimpleType(Type.Bool, Type.Nats, Type.Nats);
        } else if (c.equals(PFHelper.TRUE.getSym())) {
            return FunctionSymbolSimpleType.Bool;
        } else if (c.equals(PFHelper.ITE)){
            return new FunctionSymbolSimpleType(Type.Nats, Type.Bool, Type.Nats, Type.Nats);
        } else {
            assert this.types.containsKey(c);
            return this.types.get(c);
        }
    }

    public FunctionSymbolSimpleType lookupType(FunctionSymbol c) {
        assert types.containsKey(c);
        return types.get(c);
    }

    public List<Type> lookupArgumentTypes(FunctionSymbol symbol) {
        return lookupType(symbol).getArgumentTypes();
    }

    public CollectionMap<Type, FunctionSymbol> group(Set<FunctionSymbol> symbols) {
        CollectionMap<Type, FunctionSymbol> res = new CollectionMap<>();
        for (FunctionSymbol s : symbols) {
            res.add(this.getReturnType(s), s);
        }
        return res;
    }

    @Override
    public Iterator<Type> iterator() {
        return this.getTypes().iterator();
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        for (Entry<FunctionSymbol, FunctionSymbolSimpleType> e : this.types.entrySet()) {
            FunctionSymbol f = e.getKey();
            FunctionSymbolSimpleType type = e.getValue();
            if (!type.equals(FunctionSymbolSimpleType.Nats)) {
                sb.append(f.export(eu));
                sb.append(eu.escape(" :: "));
                sb.append(type.export(eu));
                sb.append(eu.linebreak());
            }
        }
        return sb.toString();
    }

    @Override
    public TrsTypes clone() {
        TrsTypes res = new TrsTypes();
        res.types.putAll(this.types);
        return res;
    }

    public void remove(FunctionSymbol f) {
        this.types.remove(f);
    }

}
