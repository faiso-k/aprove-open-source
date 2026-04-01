package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.oldframework.BasicStructures.*;

public class FactArg extends Fact {

    private final FunctionSymbol f;
    private final int i;

    public FactArg(FunctionSymbol f, int i) {
        this.f = f;
        this.i = i;
    }

    @Override
    public String toString() {
        return this.f.getName()+"/"+this.i;
    }

}
