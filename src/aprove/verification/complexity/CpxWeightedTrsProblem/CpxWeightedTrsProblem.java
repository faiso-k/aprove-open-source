package aprove.verification.complexity.CpxWeightedTrsProblem;

import static java.util.stream.Collectors.toSet;

import java.util.LinkedHashSet;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A TRS with weighted rules (weights are natural numbers).
 * This can express relative rewriting by using rules with weight 0.
 *
 * @author mnaaf
 *
 */
public class CpxWeightedTrsProblem extends DefaultBasicObligation
    implements HasTRSTerms, HasRules<WeightedRule>, HasDefinedSymbols, HasVariables
{
    protected final ImmutableSet<WeightedRule> R;
    protected final boolean innermost;

    // signature is usually the set of function symbols occurring in R, but can be larger
    protected final ImmutableSet<FunctionSymbol> signature;

    // calculated values
    protected final ImmutableSet<FunctionSymbol> defSymbols;

    protected CpxWeightedTrsProblem(
            String shortName,
            String longName,
            final ImmutableSet<WeightedRule> R,
            final ImmutableSet<FunctionSymbol> signature,
            final boolean innermost) {
        super(shortName,longName);
        this.R = R;
        this.innermost = innermost;

        assert(signature.containsAll(CollectionUtils.getFunctionSymbols(this.R)));
        this.signature = signature;

        final Set<FunctionSymbol> defSymbols = CollectionUtils.getRootSymbols(this.R);
        this.defSymbols = ImmutableCreator.create(defSymbols);
    }

    private CpxWeightedTrsProblem(
            final ImmutableSet<WeightedRule> R,
            final ImmutableSet<FunctionSymbol> signature,
            final boolean innermost) {
        this("CpxWeightedTrs","CpxWeightedTrs",R,signature,innermost);
    }

    public static CpxWeightedTrsProblem create(final ImmutableSet<WeightedRule> R,
            final ImmutableSet<FunctionSymbol> signature, final boolean innermost) {
        return new CpxWeightedTrsProblem(R, signature, innermost);
    }

    public static CpxWeightedTrsProblem create(final ImmutableSet<WeightedRule> R, final boolean innermost) {
        ImmutableSet<FunctionSymbol> signature = ImmutableCreator.create(CollectionUtils.getFunctionSymbols(R));
        return new CpxWeightedTrsProblem(R, signature, innermost);
    }

    @Override
    public String getStrategyName() {
        return "cpxweightedtrs";
    }

    public boolean isInnermost() {
        return this.innermost;
    }

    @Override
    public ImmutableSet<WeightedRule> getRules() {
        return this.R;
    }

    public Set<Rule> getUnweightedRules() {
        return this.R.stream().map(r -> r.getRule()).collect(Collectors.toSet());
    }

    @Override
    public ImmutableSet<FunctionSymbol> getDefinedSymbols() {
        return this.defSymbols;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    public Set<Variable> getVariables() {
        Set<Variable> result = new LinkedHashSet<Variable>();
        for (WeightedRule rule : this.R) {
            result.addAll(rule.getVariables());
        }
        return result;
    }

    //the same as above, just with the actual type
    public Set<TRSVariable> getTRSVariables() {
        Set<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        for (WeightedRule rule : this.R) {
            result.addAll(rule.getTRSVariables());
        }
        return result;
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(getProofPurposeDescriptor().export(o));
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

        s.append("Rewrite Strategy: " +
                (this.innermost ? "INNERMOST" : "FULL" ));

        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Set<? extends TRSTerm> getTerms() {
        return CollectionUtils.getTerms(this.R);
    }

    public boolean isLeftLinear() {
        for (WeightedRule r: this.R) {
            if (!r.getLeft().isLinear()) {
                return false;
            }
        }
        return true;
    }

    public boolean isBasic(TRSTerm term) {
        if (term.isVariable()) {
            return false;
        }
        TRSFunctionApplication funapp = (TRSFunctionApplication)term;
        if (!defSymbols.contains(funapp.getRootSymbol())) {
            return false;
        }
        return funapp.getNonRootFunctionSymbols().stream().allMatch(x -> !defSymbols.contains(x));
    }

    public boolean isDefined(FunctionSymbol f) {
        return defSymbols.contains(f);
    }

    public boolean isConstructorSystem() {
        for (WeightedRule r: getRules()) {
            if (!isBasic(r.getLeft())) {
                return false;
            }
        }
        return true;
    }

    public Set<WeightedRule> getRulesFor(FunctionSymbol root) {
        return this.R.stream().filter(r -> r.getRootSymbol().equals(root)).collect(Collectors.toSet());
    }

    public Set<Rule> getUnweightedRulesFor(FunctionSymbol root) {
        return this.R.stream().filter(r -> r.getRootSymbol().equals(root)).map(r -> r.getRule()).collect(Collectors.toSet());
    }

    public Set<String> getUsedNames() {
        Set<String> res = new LinkedHashSet<>();
        res.addAll(getSignature().stream().map(x -> x.getName()).collect(toSet()));
        res.addAll(getTerms().stream().flatMap(t -> t.getVariables().stream().map(x -> x.getName())).collect(toSet()));
        return res;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this,
                "Runtime Complexity " + (this.innermost ? "(innermost)" : "(full)"));
    }

}
