package aprove.verification.oldframework.PropositionalLogic;

import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

public interface ValueCache<T> {

    public boolean assertValue(AbstractVariable<T> var, boolean one);
    public Formula<T> evaluate(AbstractVariable<T> var);
    public void update(Formula<T> formula);
    public ValueCache<T> copy();
    public FormulaFactory<T> getFactory();

}
