package aprove.solver.DiophantineSATConverters;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Conversion from Diophantine problems to SAT problems using
 * the initial (now deprecated) limited-depth encoding of
 * the beginning of 2006.
 *
 * @author Carsten Fuhs
 */
public class FLATConverter extends DiophantineSATConverter {

    @ParamsViaArgumentObject
    public FLATConverter(Arguments arguments) {
        super(arguments);
    }

    @Override
    public PoloSatConverter getPoloSatConverter(FormulaFactory<None> factory,
            Map<String, BigInteger> ranges, BigInteger defaultRange) {
        return SPCToFormulaConverter.create(factory,
                defaultRange.bitLength());
    }
}
