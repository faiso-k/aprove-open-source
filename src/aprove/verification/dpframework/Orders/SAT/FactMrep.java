package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.oldframework.BasicStructures.*;

public class FactMrep extends Fact {

    private final FunctionSymbol f;
    private final int i, l;

    public FactMrep(FunctionSymbol f, int i, int l) {
        this.f = f;
        this.i = i;
        this.l = l;
    }

    @Override
    public String toString() {
        return "Mrep("+this.f.getName()+","+this.i+","+this.l+")";
    }

}
