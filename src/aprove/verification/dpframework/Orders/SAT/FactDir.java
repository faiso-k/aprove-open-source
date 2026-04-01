package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.oldframework.BasicStructures.*;

public class FactDir extends Fact {

    private final FunctionSymbol f;

    protected FactDir(FunctionSymbol f) {
        this.f = f;
    }

    @Override
    public String toString() {
        return "dir("+this.f.getName()+")";
    }


}
