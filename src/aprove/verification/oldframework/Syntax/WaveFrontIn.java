package aprove.verification.oldframework.Syntax;


public class WaveFrontIn extends MetaFunctionSymbol {

    public static WaveFrontIn create(String name, int arity) {
        return new WaveFrontIn(name, arity);
    }

    protected WaveFrontIn(String name, int arity) {
        super(name, arity);
    }

    @Override
    public boolean isWaveFrontIn(){
        return true;
    }

    @Override
    public boolean equals(Object that) {

        if(that instanceof WaveFrontIn){
            return ((WaveFrontIn)that).isWaveFrontIn();
        }

        return false;
    }
}
