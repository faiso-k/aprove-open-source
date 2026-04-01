package aprove.verification.oldframework.WeightedIntTrs;

import static java.util.stream.Collectors.toSet;

import java.util.Collection;
import java.util.Optional;
import java.util.Set;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

public abstract class AbstractWeightedIntTermSystem<T extends AbstractWeightedIntRule<T>> extends DefaultBasicObligation {

    private Optional<FreshNameGenerator> fng = Optional.empty();

    protected String name;
    protected Set<T> rules;
    protected TRSFunctionApplication startTerm;

    public AbstractWeightedIntTermSystem(String shortOblName, String longOblName, String problemName, Set<T> rules, TRSFunctionApplication startTerm) {
        super(shortOblName, longOblName);
        this.name = problemName;
        this.rules = rules;
        this.startTerm = startTerm;
    }

    public abstract AbstractWeightedIntTermSystem<T> copyWithNewRules(Collection<T> newRules);

    public abstract AbstractWeightedIntTermSystem<T> copyWithNewRules(Collection<T> newRules, TRSFunctionApplication newStartTerm);

    public String getName() {
        return name;
    }

    public Set<T> getRules() {
        return rules;
    }

    public TRSFunctionApplication getStartTerm() {
        return startTerm;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination or Complexity");
    }

    public boolean isEmpty() {
        return rules.isEmpty();
    }

    public Set<TRSVariable> getVariables() {
        return rules.stream().flatMap(x -> x.getVariables().stream()).collect(toSet());
    }

    public Set<FunctionSymbol> getFunctionSymbols() {
        return rules.stream().flatMap(x -> x.getFunctionSymbols().stream()).collect(toSet());
    }

    private Set<HasName> getUsedNames() {
        return rules.stream().flatMap(x -> x.getUsedNames().stream()).collect(toSet());
    }

    public String getFreshName(String old) {
        if (!this.fng.isPresent()) {
            this.fng = Optional.of(new FreshNameGenerator(getUsedNames(), FreshNameGenerator.FRIENDLYNAMES));
        }
        return fng.get().getFreshName(old, false);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((rules == null) ? 0 : rules.hashCode());
        result = prime * result + ((startTerm == null) ? 0 : startTerm.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        AbstractWeightedIntTermSystem<?> other = (AbstractWeightedIntTermSystem<?>) obj;
        if (rules == null) {
            if (other.rules != null)
                return false;
        } else if (!rules.equals(other.rules))
            return false;
        if (startTerm == null) {
            if (other.startTerm != null)
                return false;
        } else if (!startTerm.equals(other.startTerm))
            return false;
        return true;
    }

}
