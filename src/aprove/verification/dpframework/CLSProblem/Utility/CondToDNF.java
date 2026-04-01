package aprove.verification.dpframework.CLSProblem.Utility;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.*;

/**
 * Transforms a CLS condition into DNF.
 *
 * FIXME: Document condition format
 * @author noschinski
 *
 */
public class CondToDNF {

    /**
     * Remove ugly Ceq(Cgt(x,y), 0) terms
     */
    public static final TRSEval CEQ2NOT_NORMALIZER;

    /**
     * Rules describing a rewrite of a CLS condition into DNF
     */
    public static final TRSEval DNF_TRS;

    static {
        String ruledef =
            "(VAR x y z)\n" +
            "(RULES\n" +
            "    Cle(x, y) -> Cge(y, x)\n" +
            "    Clt(x, y) -> Cgt(y, x)\n" +
            "    Not(Not(x)) -> x\n" +
            "    Not(Ceq(x, y)) -> Or(Cgt(x, y), Cgt(y, x))\n" +
            "    Not(Cge(x, y)) -> Cgt(y, x)\n" +
            "    Not(Cgt(x, y)) -> Cge(y, x)\n" +
            "    Not(Or(x, y)) -> And(Not(x), Not(y))\n" +
            "    Not(And(x, y)) -> Or(Not(x), Not(y))\n" +
            "    And(0, x) -> 0\n" +
            "    And(1, x) -> x\n" +
            "    And(x, 0) -> 0\n" +
            "    And(x, 1) -> x\n" +
            "    Or(0, x) -> x\n" +
            "    Or(1, x) -> 1\n" +
            "    Or(x, 0) -> x\n" +
            "    Or(x, 1) -> 1\n" +
            "    And(Or(x, y), z) -> Or(And(x, z), And(y, z))\n" +
            "    And(x, Or(y, z)) -> Or(And(x, y), And(x, z))\n" +
            ")";

        DNF_TRS = new TRSEval(ruledef);

        ruledef =
            "(VAR x y)\n" +
            "(RULES\n" +
            "    Ceq(Clt(x, y), 0) -> Cge(x, y)\n" +
            "    Ceq(Cle(x, y), 0) -> Cgt(x, y)\n" +
            "    Ceq(Ceq(x, y), 0) -> Not(Ceq(x, y))\n" +
            "    Ceq(Cge(x, y), 0) -> Clt(x, y)\n" +
            "    Ceq(Cgt(x, y), 0) -> Cle(x, y)\n" +
            ")";

        CEQ2NOT_NORMALIZER = new TRSEval(ruledef);
    }

    public static TRSTerm transform(TRSTerm t) {
        TRSTerm tmp1 = CondToDNF.CEQ2NOT_NORMALIZER.normalize(t);
        TRSTerm tmp2 = CondToDNF.DNF_TRS.normalize(tmp1);
        return tmp2;
    }
}
