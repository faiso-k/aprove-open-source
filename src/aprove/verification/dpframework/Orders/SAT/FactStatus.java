package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.oldframework.BasicStructures.*;

public class FactStatus extends Fact {

    private final FunctionSymbol f;

    protected FactStatus(FunctionSymbol f) {
        this.f = f;
    }

    @Override
    public String toString() {
        return "mul("+this.f.getName()+")";
    }


}
