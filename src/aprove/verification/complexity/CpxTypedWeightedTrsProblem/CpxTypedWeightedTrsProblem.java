package aprove.verification.complexity.CpxTypedWeightedTrsProblem;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.CpxWeightedTrsProblem.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * A TRS complexity problem with type information and weighted rules.
 * Relative rules can be expressed using weight 0.
 *
 * @author mnaaf
 *
 */
public class CpxTypedWeightedTrsProblem extends CpxWeightedTrsProblem {

    // additional type information
    private final TrsTypes types;

    // computed fields
    private final ImmutableSet<FunctionSymbol> constructors;

    private CpxTypedWeightedTrsProblem(
            final ImmutableSet<WeightedRule> R,
            final ImmutableSet<FunctionSymbol> signature,
            final TrsTypes types,
            final boolean innermost) {
        super("CpxTypedWeightedTrs","CpxTypedWeightedTrs",R,signature,innermost);
        this.types = types;

        Set<FunctionSymbol> ctors = new LinkedHashSet<>();
        ctors.addAll(signature);
        ctors.removeAll(this.defSymbols);
        this.constructors = ImmutableCreator.create(ctors);
    }

    public static CpxTypedWeightedTrsProblem create(
            final ImmutableSet<WeightedRule> R,
            final ImmutableSet<FunctionSymbol> signature,
            final TrsTypes types,
            final boolean innermost) {
        return new CpxTypedWeightedTrsProblem(R,signature,types,innermost);
    }

    public static CpxTypedWeightedTrsProblem create(
            final ImmutableSet<WeightedRule> R,
            final TrsTypes types,
            final boolean innermost) {
        ImmutableSet<FunctionSymbol> signature = ImmutableCreator.create(CollectionUtils.getFunctionSymbols(R));
        return new CpxTypedWeightedTrsProblem(R,signature,types,innermost);
    }

    //clones this instance but ensures that every type has a constant constructor (contained in the signature)
    public CpxTypedWeightedTrsProblem cloneWithConstantConstructors() {
        FreshNameGenerator fng = new FreshNameGenerator(this.getUsedNames(),FreshNameGenerator.APPEND_NUMBERS);
        Set<FunctionSymbol> signature = new LinkedHashSet<>(this.signature);
        TrsTypes types = this.cloneTypes();
        for (Type type : types.getTypes()) {
            if (this.getConstantConstructors(type).isEmpty()) {
                FunctionSymbol fresh = FunctionSymbol.create(fng.getFreshName("const",false),0);
                signature.add(fresh);
                types.declare(fresh, new FunctionSymbolSimpleType(type));
            }
        }
        return CpxTypedWeightedTrsProblem.create(this.R, ImmutableCreator.create(signature), types, this.innermost);
    }

    public boolean isInnermost() {
        return this.innermost;
    }

    public ImmutableSet<FunctionSymbol> getConstructors() {
        return this.constructors;
    }

    public boolean isConstructor(FunctionSymbol fun) {
        return this.constructors.contains(fun);
    }

    public TrsTypes cloneTypes() {
        return types.clone();
    }

    public Set<FunctionSymbol> getConstantConstructors() {
        Set<FunctionSymbol> res = new LinkedHashSet<>();
        for (FunctionSymbol c : constructors) {
            if (c.getArity() == 0) {
                res.add(c);
            }
        }
        return res;
    }

    public Set<FunctionSymbol> getConstantConstructors(Type t) {
        Set<FunctionSymbol> res = new LinkedHashSet<>();
        for (FunctionSymbol c : constructors) {
            if (c.getArity() == 0 && types.lookupType(c).getReturnType().equals(t)) {
                res.add(c);
            }
        }
        return res;
    }

    public Set<FunctionSymbol> getNonConstantConstructors(Type t) {
        Set<FunctionSymbol> res = new LinkedHashSet<>();
        for (FunctionSymbol c : constructors) {
            if (c.getArity() > 0 && types.lookupType(c).getReturnType().equals(t)) {
                res.add(c);
            }
        }
        return res;
    }

    public List<Type> getArgumentTypes(FunctionSymbol symbol) {
        return types.lookupArgumentTypes(symbol);
    }

    public FunctionSymbolSimpleType getType(FunctionSymbol symbol) {
        return types.lookupType(symbol);
    }

    public boolean hasNonConstantConstructor(Type type) {
        return !getNonConstantConstructors(type).isEmpty();
    }

    public boolean hasConstantConstructor(Type type) {
        return !getConstantConstructors(type).isEmpty();
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Runtime Complexity Weighted TRS with Types."));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        s.append(o.export("The TRS has the following type information:"));
        s.append(o.cond_linebreak());
        s.append(o.indent(this.types.export(o)));
        s.append(o.cond_linebreak());

        s.append("Rewrite Strategy: " +
                (this.innermost ? "INNERMOST" : "FULL" ));

        return s.toString();
    }

    @Override
    public String getStrategyName() {
        return "cpxtypedweightedtrs";
    }

}
