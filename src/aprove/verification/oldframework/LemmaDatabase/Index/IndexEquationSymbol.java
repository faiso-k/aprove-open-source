package aprove.verification.oldframework.LemmaDatabase.Index;

public class IndexEquationSymbol extends IndexSymbol {

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
        return true;
    }

    @Override
    public boolean isAVariableSymbol() {
        return false;
    }

    @Override
    public boolean isATruthValue() {
        return false;
    }

    @Override
    public boolean equals(Object that) {
        if(that instanceof IndexSymbol) {
            return ((IndexSymbol)that).isAEquation();
        }else{
            return false;
        }
    }

    @Override
    public String toString() {
        return "=";
    }
}
