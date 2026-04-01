package aprove.verification.oldframework.LemmaDatabase.Index;

public class IndexFunctionSymbol extends IndexSymbol {

    protected String name;

    public IndexFunctionSymbol(String name) {
        this.name = name;
    }

    @Override
    public boolean isAFunctionSymbol() {
        return true;
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
        return false;
    }

    @Override
    public boolean isATruthValue() {
        return false;
    }

    public String getName() {
        return this.name;
    }

    @Override
    public boolean equals(Object that) {
        if(that instanceof IndexSymbol) {
            return ((IndexSymbol)that).isAFunctionSymbol() && ((IndexFunctionSymbol)that).getName().equals(this.name);
        }else{
            return false;
        }
    }

    @Override
    public String toString() {
        return this.name;
    }

}
