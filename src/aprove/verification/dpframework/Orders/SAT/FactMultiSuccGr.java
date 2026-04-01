package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.dpframework.BasicStructures.*;

public class FactMultiSuccGr extends Fact {

    private final TRSFunctionApplication s, t;
    private final int i, j;

    public FactMultiSuccGr(TRSFunctionApplication s, TRSFunctionApplication t, int i, int j) {
        this.s = s;
        this.t = t;
        this.i = i;
        this.j = j;
    }

    @Override
    public String toString() {
        return "MultiSuccGr("+this.s+","+this.t+","+","+this.i+","+this.j+")";
    }

}
