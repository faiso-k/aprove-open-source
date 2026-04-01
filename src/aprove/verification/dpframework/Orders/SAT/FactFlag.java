package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.oldframework.BasicStructures.*;

public class FactFlag extends Fact {

    private final FunctionSymbol f;

    protected FactFlag(FunctionSymbol f) {
        this.f = f;
    }

    @Override
    public String toString() {
        return "flag("+this.f.getName()+")";
    }

}
