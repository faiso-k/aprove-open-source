package aprove.solver.DiophantineSATConverters;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Conversion from Diophantine problems to SAT problems as described
 * in the PROLE'07 paper by Lucas and Navarro from Valencia.
 *
 * Range information is disregarded since only range 1 is supported.
 *
 * @author Carsten Fuhs
 */
public class VALENCIAConverter extends DiophantineSATConverter {

    // if p > 0 is to be encoded for searchstrict constraints:
    // encode p > 0 as such (or as p - 1 >= 0)?
    private final boolean gtAsSuch;

    @ParamsViaArgumentObject
    public VALENCIAConverter(Arguments arguments) {
        super(arguments);
        this.gtAsSuch = arguments.gtAsSuch;
    }

    @Override
    public PoloSatConverter getPoloSatConverter(FormulaFactory<None> factory,
            Map<String, BigInteger> ranges, BigInteger defaultRange) {
        PoloSatConfigInfo info = this.getPoloSatConfigInfo();
        boolean neqSearchstrict = info.getNeqSearchstrict();
        return ValenciaZeroOneConverter.create(factory,
                neqSearchstrict, this.gtAsSuch);
    }

    public static class Arguments extends DiophantineSATConverter.Arguments {
        public boolean gtAsSuch = false;
    }
}
