package aprove.verification.oldframework.LemmaDatabase.Index;


public class IndexNotSymbol extends IndexJunctorSymbol {

    @Override
    public boolean isANot() {
        return true;
    }

    @Override
    public boolean isAAnd() {
        return false;
    }

    @Override
    public boolean isAImplication() {
        return false;
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
        if( that instanceof IndexSymbol) {
            return ((IndexSymbol)that).isAJunctorSymbol() && ((IndexJunctorSymbol)that).isANot();
        }else{
            return false;
        }
    }

    @Override
    public String toString() {
        return "!";
    }

}
