package aprove.verification.dpframework.Orders.SAT;

import aprove.verification.oldframework.BasicStructures.*;

public class FactBot extends Fact {

    private FunctionSymbol f;

    public FactBot(FunctionSymbol f) {
        this.f = f;
    }

    public FunctionSymbol getFunctionSymbol() {
        return this.f;
    }

    @Override
    public String toString() {
        return "bot("+this.f.getName()+")";
    }

}
