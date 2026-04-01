package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.dpframework.BasicStructures.*;

public class FactMultiSuccEq extends Fact {

    private final TRSFunctionApplication s, t;
    private final int i, j;

    public FactMultiSuccEq(TRSFunctionApplication s, TRSFunctionApplication t, int i, int j) {
        this.s = s;
        this.t = t;
        this.i = i;
        this.j = j;
    }

    @Override
    public String toString() {
        return "MultiSuccEq("+this.s+","+this.t+","+","+this.i+","+this.j+")";
    }

}
