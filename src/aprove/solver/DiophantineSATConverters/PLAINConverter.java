package aprove.solver.DiophantineSATConverters;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Plain (as in "no fancy stuff") conversion from Diophantine problems
 * to SAT problems.
 *
 * @author Carsten Fuhs
 */
public class PLAINConverter extends DiophantineSATConverter {

    @ParamsViaArgumentObject
    public PLAINConverter(Arguments arguments) {
        super(arguments);
    }

    /**
     * @return a converter that is able to transform SPCs to formulae that
     * later can be solved by some SAT backend.
     * @param factoryParam The factory that will be used to create the formulae.
     * @param ranges The ranges of the variables.
     * @param defaultRange The range of variables not mentioned in ranges.
     */
    @Override
    public PoloSatConverter getPoloSatConverter(
            final FormulaFactory<None> factoryParam,
            final Map<String, BigInteger> ranges,
            final BigInteger defaultRange) {
        return PlainSPCToCircuitConverter.create(
                factoryParam, ranges, defaultRange,
                    this.getPoloSatConfigInfo());
    }
}
