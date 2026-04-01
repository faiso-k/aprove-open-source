package aprove.verification.oldframework.PropositionalLogic.ValueCaches;

import java.util.*;

import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

public class NoValueCache<T> implements ValueCache<T> {

    private FormulaFactory<T> factory;

    public NoValueCache(FormulaFactory<T> factory) {
        this.factory = factory;
    }

    private NoValueCache(NoValueCache<T> other) {
        this.factory = other.factory;
    }

    @Override
    public ValueCache<T> copy() {
        return new NoValueCache<T>(this);
    }

    @Override
    public boolean assertValue(AbstractVariable<T> var, boolean one) {
        return true;
    }

    @Override
    public Formula<T> evaluate(AbstractVariable<T> var) {
        return var;
    }

    @Override
    public void update(Formula<T> formula) {}

    @Override
    public boolean equals(Object o) {
        return o instanceof NoValueCache;
    }

    @Override
    public int hashCode() {
        return 0;
    }

    public String toString(Map<Variable<T>, Fact> factMap) {
        return this.toString();
    }

    @Override
    public FormulaFactory<T> getFactory() {
        return this.factory;
    }

}
