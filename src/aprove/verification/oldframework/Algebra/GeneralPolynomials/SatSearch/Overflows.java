package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Encapsulates a list of formulae which all have to become false
 * for the corresponding PolyCircuit to actually encode its
 * corresponding polynomial. This way, we can restrict the value
 * SatSearch may assign to *polynomials*.
 *
 * Used in the context of bounded arithmetic for encodings of
 * Diophantine formulae to SAT.
 *
 * @author fuhs
 */
public class Overflows {

    private List<Formula<None>> overflows;

    /**
     * Object for empty list of overflows.
     * Not necessarily unique.
     */
    public static Overflows NO_OVERFLOWS =
            new Overflows(Collections.<Formula<None>>emptyList());

    /**
     * @param overflows - will be used internally as such, so
     *  modifying the param list afterwards will lead to
     *  aliasing effects
     */
    public Overflows(List<Formula<None>> overflows) {
        this.overflows = overflows;
    }

    /**
     * @param overflows - the encapsulated lists of formulae shall be
     *  merged/concatenated into a new list
     * @return the resulting Overflows object that encapsulates
     *  the concatenation of the input overflows
     */
    public static Overflows merge(Overflows... overflows) {
        int newSize = 0;
        for (Overflows o : overflows) {
            newSize += o.overflows.size();
        }
        if (newSize == 0) {
            return Overflows.NO_OVERFLOWS;
        }

        List<Formula<None>> newList = new ArrayList<Formula<None>>(newSize);
        for (Overflows o : overflows) {
            newList.addAll(o.overflows);
        }
        Overflows res = new Overflows(newList);
        return res;
    }


    public Formula<None> ensureAllOverflowsZero(FormulaFactory<None> ff) {
        Formula<None> res = ff.buildNot(ff.buildOr(this.overflows));
        return res;
    }
}
