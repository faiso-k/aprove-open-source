package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.oldframework.BasicStructures.*;

public class FactSucc extends Fact {

    private FunctionSymbol f;
    private FunctionSymbol g;

    public FactSucc(FunctionSymbol f, FunctionSymbol g) {
        this.f = f;
        this.g = g;
    }

    public FunctionSymbol getLeft() {
        return this.f;
    }

    public FunctionSymbol getRight() {
        return this.g;
    }

    @Override
    public String toString() {
        return this.f.getName()+">"+this.g.getName();
    }

}
