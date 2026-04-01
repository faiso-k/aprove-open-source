package aprove.verification.oldframework.LemmaDatabase.Index;

public class IndexVariableSymbol extends IndexSymbol {


    public IndexVariableSymbol() {
    }

    @Override
    public boolean isAFunctionSymbol() {
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
    public boolean isAVariableSymbol() {
        return true;
    }

    @Override
    public boolean isATruthValue() {
        return false;
    }

    @Override
    public boolean equals(Object that) {
        if(that instanceof IndexSymbol) {
            return ((IndexSymbol)that).isAVariableSymbol();
        }else{
            return false;
        }
    }

    @Override
    public String toString() {
        return "*";
    }
}
