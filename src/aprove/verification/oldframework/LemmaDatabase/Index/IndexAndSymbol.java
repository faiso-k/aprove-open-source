package aprove.verification.oldframework.LemmaDatabase.Index;

public class IndexAndSymbol extends IndexJunctorSymbol{

    @Override
    public boolean isAAnd() {
        return true;
    }

    @Override
    public boolean isAEquivalence() {
        return false;
    }

    @Override
    public boolean isAImplication() {
        return false;
    }

    @Override
    public boolean isANot() {
        return false;
    }

    @Override
    public boolean isAOr() {
        return true;
    }

    @Override
    public boolean equals(Object that) {
        if(that instanceof IndexSymbol) {
            return ((IndexSymbol)that).isAJunctorSymbol() && ((IndexJunctorSymbol)that).isAAnd();
        }else{
            return false;
        }
    }

    @Override
    public String toString() {
        return "/\\";
    }

}
