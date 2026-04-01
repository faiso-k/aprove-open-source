package aprove.verification.complexity.CpxGTrsProblem;

import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class CpxGTrsProblem extends DefaultBasicObligation {

    private Set<GeneralizedRule> rules;

    public CpxGTrsProblem(Set<GeneralizedRule> rules) {
        this.rules = rules;
    }

    public Set<GeneralizedRule> getRules() {
        return rules;
    }

    @Override
    public String getStrategyName() {
        return "gruntimecomplexity";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this, "Runtime Complexity ");
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(getProofPurposeDescriptor().export(o));
        s.append(o.cond_linebreak());
        if (this.rules.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.rules, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    public Set<FunctionSymbol> getDefinedSymbols() {
        return rules.stream().map(x -> x.getRootSymbol()).collect(toSet());
    }

}
