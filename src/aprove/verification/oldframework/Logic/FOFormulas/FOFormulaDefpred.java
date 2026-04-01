package aprove.verification.oldframework.Logic.FOFormulas;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Formula with Defpred
 * @Author Andreas Kelle-Emden
 */
public class FOFormulaDefpred extends FOFormula {
    protected List<TRSVariable> args;
    protected FunctionSymbol func;
    protected FOFormula      body;

    public FOFormulaDefpred (List<TRSVariable> args, FunctionSymbol func, FOFormula body) {
        this.args = args;
        this.func = func;
        this.body = body;
    }

    @Override
    public String toString() {
        String s = "(DEFPRED (" + this.func.toString();
        for (TRSVariable v: this.args) {
            s += " "+v.toString();
        }
        return s+") " + this.body.toString() + ")";
    }

}