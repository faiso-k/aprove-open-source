package aprove.verification.oldframework.Syntax;


public abstract class MetaFunctionSymbol extends SyntacticFunctionSymbol {

    protected MetaFunctionSymbol(String name, int arity){
        super(name,arity);
    }

    @Override
    public Symbol deepcopy() {
        return null;
    }

    @Override
    public Object apply(FineSymbolVisitor fsv) {
        return fsv.caseMetaFunctionSymbol(this);
    }

    @Override
    public int getSignatureClass() {
        return 0;
    }

    @Override
    public String verboseToString() {
        return null;
    }

    public boolean isWaveHole() {
        return false;
    }

    public boolean isWaveFrontIn() {
        return false;
    }

    public boolean isWaveFrontOut() {
        return false;
    }
}
