package aprove.verification.oldframework.LemmaDatabase.Index;

public abstract class IndexJunctorSymbol extends IndexSymbol {

    @Override
    public boolean isAFunctionSymbol() {
        return false;
    }

    @Override
    public boolean isAJunctorSymbol() {
        return true;
    }

    @Override
    public boolean isAEquation() {
        return false;
    }

    @Override
    public boolean isAVariableSymbol() {
        return false;
    }

    @Override
    public boolean isATruthValue() {
        return false;
    }

    public abstract boolean isANot();

    public abstract boolean isAAnd();

    public abstract boolean isAImplication();

    public abstract boolean isAEquivalence();

    public abstract boolean isAOr();
}
