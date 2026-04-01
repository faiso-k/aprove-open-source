package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.oldframework.BasicStructures.*;

public class FactPerm extends Fact {

    private final FunctionSymbol f;
    private final int i, j;

    public FactPerm(FunctionSymbol f, int i, int j) {
        this.f = f;
        this.i = i;
        this.j = j;
    }

    @Override
    public String toString() {
        return "Perm("+this.f.getName()+","+this.i+","+this.j+")";
    }

}
