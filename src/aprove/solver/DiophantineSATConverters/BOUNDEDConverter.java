package aprove.solver.DiophantineSATConverters;

import java.math.*;
import java.util.*;

import aprove.solver.*;
import aprove.strategies.Annotations.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Bounded conversion from Diophantine problems to SAT problems.
 * Bounded insofar as we set a limit for the register length for
 * additions and multiplications and enforce that all more
 * significant bits are interpreted by 0 by any model.
 *
 * @author Carsten Fuhs
 */
public class BOUNDEDConverter extends DiophantineSATConverter {

    private final int sumBits; // max register length for sums
    private final int productBits; // max register length for products

    @ParamsViaArgumentObject
    public BOUNDEDConverter(Arguments arguments) {
        super(arguments);
        this.productBits = arguments.productBits;
        this.sumBits = arguments.sumBits;
    }

    /**
     * @return Returns the productBits.
     */
    public int getProductBits() {
        return this.productBits;
    }

    /**
     * @return Returns the sumBits.
     */
    public int getSumBits() {
        return this.sumBits;
    }

    @Override
    public PoloSatConverter getPoloSatConverter(FormulaFactory<None> factory, Map<String, BigInteger> ranges, BigInteger defaultRange) {
        return BoundedSPCToCircuitConverter.create(factory, ranges, defaultRange,
                this.sumBits, this.productBits, this.getPoloSatConfigInfo());
    }

    public static class Arguments extends DiophantineSATConverter.Arguments {
        public int productBits = Integer.MAX_VALUE;
        public int sumBits = Integer.MAX_VALUE;
    }
}
