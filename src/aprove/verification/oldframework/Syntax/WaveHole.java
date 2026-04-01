package aprove.verification.oldframework.Syntax;

public class WaveHole extends MetaFunctionSymbol {

    public static WaveHole create(String name, int arity) {
        return new WaveHole(name,arity);
    }

    protected WaveHole(String name, int arity) {
        super(name, arity);
    }

    @Override
    public boolean isWaveHole() {
        return true;
    }

    @Override
    public boolean equals(Object that) {

        if(that instanceof WaveHole){
            return ((WaveHole)that).isWaveHole();
        }

        return false;
    }
}
