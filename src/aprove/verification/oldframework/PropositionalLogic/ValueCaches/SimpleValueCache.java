package aprove.verification.oldframework.PropositionalLogic.ValueCaches;

import java.util.*;

import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

public class SimpleValueCache<T> implements ValueCache<T> {

    private Map<AbstractVariable<T>,Constant<T>> knownValues = new HashMap<AbstractVariable<T>, Constant<T>>();
    private FormulaFactory<T> factory;

    public SimpleValueCache(FormulaFactory<T> factory) {
        this.factory = factory;
    }

    private SimpleValueCache(SimpleValueCache<T> other) {
        this.knownValues = new HashMap<AbstractVariable<T>, Constant<T>>(other.knownValues);
        this.factory = other.factory;
    }

    @Override
    public ValueCache<T> copy() {
        return new SimpleValueCache<T>(this);
    }

    @Override
    public boolean assertValue(AbstractVariable<T> var, boolean one) {
        return this.knownValues.put(var, this.factory.buildConstant(one)) == null;
    }

    @Override
    public Formula<T> evaluate(AbstractVariable<T> var) {
        Constant<T> value = this.knownValues.get(var);
        if (value == null) {
            return var;
        }
        return value;
    }

    @Override
    public void update(Formula<T> formula) {
        formula.update(this, true);
    }

    @Override
    public String toString() {
        return this.knownValues.toString();
    }

    @Override
    public boolean equals(Object o) {
        SimpleValueCache<T> other = (SimpleValueCache<T>) o;
        return this.knownValues.equals(other.knownValues);
    }

    @Override
    public int hashCode() {
        return this.knownValues.hashCode();
    }

    public String toString(Map<? extends AbstractVariable<T>, Fact> factMap) {
        Map<Fact,Constant<T>> res = new HashMap<Fact, Constant<T>>();
        for (Map.Entry<AbstractVariable<T>, Constant<T>> entry : this.knownValues.entrySet()) {
            res.put(factMap.get(entry.getKey()), entry.getValue());
        }
        return res.toString();
    }

    @Override
    public FormulaFactory<T> getFactory() {
        return this.factory;
    }

}
