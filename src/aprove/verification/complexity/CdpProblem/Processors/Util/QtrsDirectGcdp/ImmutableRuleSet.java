package aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

public class ImmutableRuleSet<T extends GeneralizedRule> extends RuleSet<T> implements Immutable, ImmutableSet<T> {

    public ImmutableRuleSet(RuleSet<T> rules) {
        super(rules);
    }

    public ImmutableRuleSet(Collection<? extends T> rules) {
        super(rules);
    }

    @Override
    public boolean add(T e) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean remove(Object o) {
        throw new UnsupportedOperationException();
    }

}
