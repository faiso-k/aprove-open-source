package aprove.verification.dpframework.Orders;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * KBO with status and strict precendence
 *
 * @author Andreas Kelle-Emden
 */
public class KBOS extends QKBOS {

    public KBOS(Qoset<FunctionSymbol> precedence, Map<FunctionSymbol, BigInteger> weight, BigInteger w0, StatusMap<FunctionSymbol> status) {
        super(precedence, weight, w0, status);
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        res.append("Knuth-Bendix order "+o.cite(Citation.KBO)+" with precedence:");
        res.append(o.export(this.precedence));
        res.append(o.cond_linebreak()+"weight map:");
        res.append(o.linebreak());
        res.append(o.set(this.weightMap.entrySet(), Export_Util.RULES));
        res.append(o.cond_linebreak()+"and status map:");
        res.append(o.linebreak());
        res.append(o.export(this.statusMap));
        res.append(o.linebreak());
        res.append("The variable weight is "+this.w0);
        res.append(o.linebreak());
        return res.toString();
    }

}
