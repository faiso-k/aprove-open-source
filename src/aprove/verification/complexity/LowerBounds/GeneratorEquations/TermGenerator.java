package aprove.verification.complexity.LowerBounds.GeneratorEquations;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Creates generator symbols and can be used to create generator terms.
 */
public class TermGenerator {

    private Map<Type, FunctionSymbol> generatorSymbols = new LinkedHashMap<>();
    private Map<Type, TRSFunctionApplication> constantTerms = new LinkedHashMap<>();
    private Map<Type, TRSFunctionApplication> freshConstants = new LinkedHashMap<>();
    private LowerBoundsTrs trs;
    private RenamingCentral renamingCentral;

    public TermGenerator(LowerBoundsTrs trs, RenamingCentral renamingCentral) {
        this.trs = trs;
        this.renamingCentral = renamingCentral;
        this.initHoles();
        this.initGeneratorSymbols();
    }

    private void initHoles() {
        for (Type t : this.trs.getTypes()) {
            FunctionSymbol f = this.renamingCentral.freshConstant("hole_" + t);
            this.trs.getTypes().declare(f, new FunctionSymbolSimpleType(t));
            TRSFunctionApplication fa = TRSTerm.createFunctionApplication(f);
            this.freshConstants.put(t, fa);
        }
    }

    private TRSFunctionApplication buildConstantTerm(FunctionSymbol constructor) {
        ArrayList<TRSTerm> args = new ArrayList<>();
        for (Type argType : this.trs.getArgumentTypes(constructor)) {
            args.add(this.getConstantTerm(argType));
        }
        return TRSTerm.createFunctionApplication(constructor, args);
    }

    private void initGeneratorSymbols() {
        for (Type type: this.trs.getTypes()) {
            this.initGeneratorSymbol(type);
        }
    }

    private void initGeneratorSymbol(Type type) {
        if (!this.trs.hasRecursiveConstructor(type)) {
            return;
        }
        FunctionSymbol generatorSymbol = this.renamingCentral.freshSymbol("gen_" + type, 1);
        FunctionSymbolSimpleType generatorType = new FunctionSymbolSimpleType(type, Type.Nats);
        this.trs.getTypes().declare(generatorSymbol, generatorType);
        this.generatorSymbols.put(type, generatorSymbol);
    }

    private TRSFunctionApplication buildGeneratorTerm(Type type, TRSTerm intArg) {
        FunctionSymbol generatorSymbol = this.getGeneratorSymbol(type);
        return TRSTerm.createFunctionApplication(generatorSymbol, intArg);
    }

    public TRSFunctionApplication generate(FunctionSymbol symbol) {
        char next = 'a';
        List<Type> argTypes = this.trs.getArgumentTypes(symbol);
        ArrayList<TRSTerm> args = new ArrayList<>();
        for (int i = 0; i < symbol.getArity(); i++) {
            Type type = argTypes.get(i);
            if (this.generatorSymbols.containsKey(type)) {
                TRSTerm generatorTerm = this.buildGeneratorTerm(type, TRSTerm.createVariable(String.valueOf(next)));
                args.add(generatorTerm);
                next++;
            } else {
                args.add(this.getConstantTerm(type));
            }
        }
        return TRSTerm.createFunctionApplication(symbol, args);
    }

    FunctionSymbol getGeneratorSymbol(Type type) {
        return this.generatorSymbols.get(type);
    }

    public TRSFunctionApplication getConstantTerm(Type type) {
        if (!this.constantTerms.containsKey(type)) {
            Set<FunctionSymbol> constantSymbols = this.trs.getNonRecursiveConstructors(type);
            TRSFunctionApplication term = null;
            for (FunctionSymbol cs : constantSymbols) {
                if (term == null || this.trs.usedForPatternMatching(cs)) {
                    term = this.buildConstantTerm(cs);
                    if (this.trs.usedForPatternMatchingInNonRecursicveRule(cs, this.trs.getDependencyGraph())) {
                        break;
                    }
                }
            }
            if (term == null) {
                term = this.freshConstants.get(type);
            }
            this.constantTerms.put(type, term);
        }
        return this.constantTerms.get(type);
    }

    public boolean isGeneratorSymbol(FunctionSymbol rootSymbol) {
        return generatorSymbols.containsValue(rootSymbol);
    }

}
