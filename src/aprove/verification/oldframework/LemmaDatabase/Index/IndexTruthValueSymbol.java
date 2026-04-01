package aprove.verification.oldframework.LemmaDatabase.Index;

public class IndexTruthValueSymbol extends IndexSymbol {

    protected boolean value;

    public IndexTruthValueSymbol(boolean value) {
        this.value = value;
    }

    @Override
    public boolean isAFunctionSymbol() {
        return false;
    }

    @Override
    public boolean isAVariableSymbol() {
        return false;
    }

    @Override
    public boolean isAJunctorSymbol() {
        return false;
    }

    @Override
    public boolean isAEquation() {
        return false;
    }

    @Override
    public boolean isATruthValue() {
        return true;
    }

    public boolean getValue() {
        return this.value;
    }

    @Override
    public boolean equals(Object that) {
        if( (that instanceof IndexSymbol) && ((IndexSymbol)that).isATruthValue() ){
            return this.value  == ((IndexTruthValueSymbol)that).value;
        }
        return false;
    }

    @Override
    public String toString() {
        return this.value ? "True" : "False";
    }
}
