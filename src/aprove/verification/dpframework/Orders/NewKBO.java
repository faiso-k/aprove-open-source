package aprove.verification.dpframework.Orders;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * New implementation of the KBO with strict precedence for use with SMT solvers
 *
 * @author Andreas Kelle-Emden
 */
public class NewKBO extends QKBO {

    public NewKBO(Qoset<FunctionSymbol> precedence, Map<FunctionSymbol, BigInteger> weight, BigInteger w0) {
        super(precedence, weight, w0);
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        res.append("Knuth-Bendix order "+o.cite(Citation.KBO)+" with precedence:");
        res.append(o.export(this.precedence));
        res.append(o.cond_linebreak()+"and weight map:");
        res.append(o.linebreak());
        res.append(o.set(this.weightMap.entrySet(), Export_Util.RULES));
        res.append(o.linebreak());
        res.append("The variable weight is "+this.w0);
        return res.toString();
    }

}
