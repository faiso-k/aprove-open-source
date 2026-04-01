package aprove.verification.oldframework.LemmaDatabase.Index;

public class IndexImplicationSymbol extends IndexJunctorSymbol {

    @Override
    public boolean isANot() {
        return false;
    }

    @Override
    public boolean isAAnd() {
        return false;
    }

    @Override
    public boolean isAImplication() {
        return true;
    }

    @Override
    public boolean isAEquivalence() {
        return false;
    }

    @Override
    public boolean isAOr() {
        return true;
    }

    @Override
    public boolean equals(Object that) {
        return ((IndexSymbol)that).isAJunctorSymbol() && ((IndexJunctorSymbol)that).isAImplication();
    }

    @Override
    public String toString() {
        return "->";
    }
}
