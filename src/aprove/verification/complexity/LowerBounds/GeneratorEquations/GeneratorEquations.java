package aprove.verification.complexity.LowerBounds.GeneratorEquations;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Equation;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;


public class GeneratorEquations implements Iterable<Equation>, Exportable {

    private static final TRSVariable VAR = TRSTerm.createVariable("x");

    private Set<Equation> generatorEquations = new LinkedHashSet<>();
    private TermGenerator termGenerator;
    private LowerBoundsTrs trs;

    public GeneratorEquations(LowerBoundsTrs trs, TermGenerator termGenerator) {
        this.trs = trs;
        this.termGenerator = termGenerator;
        this.init();
    }

    public TermGenerator getTermGenerator() {
        return this.termGenerator;
    }

    private void init() {
        for (Type type: this.trs.getTypes()) {
            if (type != Type.Nats) {
                Set<FunctionSymbol> succSymbols = this.trs.getRecursiveConstructors(type);
                FunctionSymbol succSymbol = null;
                for (FunctionSymbol s: succSymbols) {
                    if (succSymbol == null || this.trs.usedForPatternMatching(s)) {
                        succSymbol = s;
                        if (this.trs.usedForPatternMatchingInRecursicveRule(s, this.trs.getDependencyGraph())) {
                            break;
                        }
                    }
                }
                if (succSymbol != null) {
                    this.buildRuleForBaseCase(type);
                    this.buildRuleForInductiveCase(succSymbol);
                }
            }
        }
    }

    private void buildRuleForBaseCase(Type type) {
        FunctionSymbol generatorSymbol = this.termGenerator.getGeneratorSymbol(type);
        TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(generatorSymbol, PFHelper.ZERO.getTerm());
        TRSFunctionApplication rhs = this.termGenerator.getConstantTerm(type);
        this.generatorEquations.add(new Equation(lhs, rhs));
    }

    private void buildRuleForInductiveCase(FunctionSymbol succSymbol) {
        FunctionSymbolSimpleType type = this.trs.getType(succSymbol);
        FunctionSymbol generatorSymbol = this.termGenerator.getGeneratorSymbol(type.getReturnType());
        TRSTerm varPlusOne = TRSTerm.createFunctionApplication(PFHelper.ADD, GeneratorEquations.VAR, PFHelper.ONE.getTerm());
        TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(generatorSymbol, varPlusOne);
        ArrayList<TRSTerm> succArgs = new ArrayList<>();
        TRSFunctionApplication generatorTerm = TRSTerm.createFunctionApplication(generatorSymbol, GeneratorEquations.VAR);
        List<Type> argTypes = type.getArgumentTypes();
        int recursivePosition = -1;
        int recursiveUsages = -1;
        for (int i = argTypes.size() - 1; i >= 0; i--) {
            Type t = argTypes.get(i);
            if (t.equals(type.getReturnType())) {
                int tmpRecursiveUsages = this.trs.recursiveCallsOnArguments(succSymbol, i);
                if (tmpRecursiveUsages > recursiveUsages) {
                    recursivePosition = i;
                    recursiveUsages = tmpRecursiveUsages;
                }
            }
        }
        for (int i = 0; i < argTypes.size(); i++) {
            if (i == recursivePosition) {
                succArgs.add(generatorTerm);
            } else {
                Type t = argTypes.get(i);
                succArgs.add(this.termGenerator.getConstantTerm(t));
            }
        }
        TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(succSymbol, succArgs);
        this.generatorEquations.add(new Equation(lhs, rhs));
    }

    @Override
    public Iterator<Equation> iterator() {
        return this.generatorEquations.iterator();
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder();
        for (Equation eq: this.generatorEquations) {
            sb.append(eq.export(eu));
            sb.append(eu.linebreak());
        }
        return sb.toString();
    }

}
