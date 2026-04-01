package aprove.verification.dpframework.CLSProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CLSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

public class CLSProblem extends DefaultBasicObligation {

    private Set<ConditionalRule> rules;
    private Set<TRSFunctionApplication> initialTerms;

    private volatile Set<PredefinedFunctions> usedPredefinedFunctions;

    private CLSProblem(Set<ConditionalRule> rules, Set<TRSFunctionApplication> initialTerms) {
        super("CLS","Clousot");
        this.rules = rules;
        this.initialTerms = initialTerms;

                EnumSet<PredefinedFunctions> usedPredefinedSymbols =
                    EnumSet.noneOf(PredefinedFunctions.class);
                Set<FunctionSymbol> usedSymbols = CollectionUtils.getFunctionSymbols(this.getRules());
                usedSymbols.addAll(CollectionUtils.getFunctionSymbols(this.getInitialTerms()));
                for (FunctionSymbol fs : usedSymbols) {
                    PredefinedFunctions elem = PredefinedFunctions.getElem(fs);
                    if (elem != null) {
                        usedPredefinedSymbols.add(elem);
                    }
                }
                this.usedPredefinedFunctions = usedPredefinedSymbols;

    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder("(RULES");
        sb.append(o.set(this.rules, Export_Util.RULES));
        sb.append(")");
        sb.append(o.linebreak());
        sb.append("(INITIAL");
        sb.append(o.set(this.initialTerms, Export_Util.NICE_SET));
        sb.append(")");
        sb.append(o.linebreak());
        return sb.toString();
    }

    public static CLSProblem create(Set<ConditionalRule> rules, Set<TRSFunctionApplication> initialTerms) {
        return new CLSProblem(rules, initialTerms);
    }

    public Set<ConditionalRule> getRules() {
        return this.rules;
    }

    public Set<TRSFunctionApplication> getInitialTerms() {
        return this.initialTerms;
    }

    /**
     * Returns a set describing the predefined function symbols occurring in this problem.
     */
    public EnumSet<PredefinedFunctions> getUsedPredefinedFunctions() {
/*
        if (this.usedPredefinedFunctions == null) {
            synchronized (this) {
                EnumSet<PredefinedFunctions> usedPredefinedSymbols =
                    EnumSet.noneOf(PredefinedFunctions.class);
                Set<FunctionSymbol> usedSymbols = Collections.getFunctionSymbols(getRules());
                usedSymbols.addAll(Collections.getFunctionSymbols(getInitialTerms()));
                for (FunctionSymbol fs : usedSymbols) {
                    PredefinedFunctions elem = PredefinedFunctions.getElem(fs);
                    if (elem != null) {
                        usedPredefinedSymbols.add(elem);
                    }
                }
                this.usedPredefinedFunctions = usedPredefinedSymbols;
            }
        }
*/
        return EnumSet.copyOf(this.usedPredefinedFunctions);
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "cls";
    }
}
