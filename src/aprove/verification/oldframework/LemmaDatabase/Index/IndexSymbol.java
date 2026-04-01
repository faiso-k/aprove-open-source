package aprove.verification.oldframework.LemmaDatabase.Index;

public abstract class IndexSymbol {

    public abstract boolean isAFunctionSymbol();

    public abstract boolean isAVariableSymbol();

    public abstract boolean isAJunctorSymbol();

    public abstract boolean isAEquation();

    public abstract boolean isATruthValue();

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

}
