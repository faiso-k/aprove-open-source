package aprove.verification.oldframework.Syntax;


public class WaveFrontOut extends MetaFunctionSymbol {

    public static WaveFrontOut create(String name, int arity) {
        return new WaveFrontOut(name, arity);
    }

    protected WaveFrontOut(String name, int arity) {
        super(name, arity);
    }

    @Override
    public boolean isWaveFrontOut() {
        return true;
    }

    @Override
    public boolean equals(Object that) {

        if(that instanceof WaveFrontOut){
            return ((WaveFrontOut)that).isWaveFrontOut();
        }

        return false;
    }
}
