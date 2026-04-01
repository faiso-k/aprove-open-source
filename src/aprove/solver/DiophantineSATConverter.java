package aprove.solver;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.PoloSatConfigInfo.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Abstract superclass for strategy parameters for SatConverter
 * as in the strategy
 *
 *     main = QDPReductionPair[Order = POLO[Engine = <some SAT engine>, SatConverter = <some way of encoding SPCs to SAT>[<possibly some options>]]]
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class DiophantineSATConverter {
    /**
     * If the converter is defined in a strategy, the factory that should be
     * used will be created by this creator.
     */
    private final FormulaFactoryCreator factoryCreator;

    // true: use (A iff B); false: use (A and not B) inside GT encoding
    private final boolean useIFFsInGT;

    // there are several ways of encoding GT
    private final GTMode gtMode;

    // how do we encode n-ary sums?
    private final SumType sumType;

    // do we encode powers as combs? (if not, repeated binary squaring is used)
    private final boolean powersAsComb;

    // use times encoding of 11/06
    // -> note: beware of naming anything "new", it won't be new for long ;-)
    private final boolean newTimes;

    // use list appending for products instead of naive addition
    // where available?
    private final boolean appendForTimes;

    // keep track of maximum intermediate values?
    private final boolean tracking;

    // perform product abstraction?
    private final boolean productAbstraction;

    // true:  use "not and p_i = q_i" for searchstrict
    // false: use "or p_i > q_i" for searchstrict
    private final boolean neqSearchstrict;

    // Use shifts instead of multiplication?
    private final boolean useShifts;

    // Shall shifts be used for binary representations?
    private final boolean useBinaryShifts;

    // Shall times two be hardcoded? (Avoids XOrs in SAT formula)
    private final boolean useTimesTwoHardcoded;

    // How shall the restrictions for unary shifts be encoded?
    private final UNARY_MODE unaryMode;

    // Should we use the new encoding for unary powers?
    private final boolean newUnaryPower;

    // encode indefinites in unary?
    // (note: this parameter is unrelated to the above other parameters
    // with "unary" in their name; they are only relevant for the shift-based
    // encoding for powers of two)
    private final boolean unaryIndefinites;

    public DiophantineSATConverter(final Arguments arguments) {
        this.appendForTimes = arguments.appendForTimes;
        this.factoryCreator = arguments.formulaFactory;
        this.gtMode = arguments.gtMode;
        this.neqSearchstrict = arguments.neqSearchstrict;
        this.newTimes = arguments.newTimes;
        this.powersAsComb = arguments.powersAsComb;
        this.productAbstraction = arguments.productAbstraction;
        this.sumType = arguments.sumType;
        this.tracking = arguments.tracking;
        this.useIFFsInGT = arguments.useIFFsInGT;
        this.useShifts = arguments.useShifts;
        this.useBinaryShifts = arguments.useBinaryShifts;
        this.useTimesTwoHardcoded = arguments.useTimesTwoHardcoded ;
        this.unaryMode = arguments.unaryMode;
        this.newUnaryPower = arguments.newUnaryPower;
        this.unaryIndefinites = arguments.unaryIndefinites;
    }
    /**
     * Gets a PoloSatConverter that corresponds to this and that uses
     * factory as FormulaFactory.
     *
     * @param factory
     * @param ranges - maps indefinites to maximum values
     * @param defaultRange - for those indefinites that do not occur in
     *  the keySet of ranges
     * @return a corresponding PoloSatConverter
     */
    public abstract PoloSatConverter getPoloSatConverter(FormulaFactory<None> factory,
            Map<String, BigInteger> ranges, BigInteger defaultRange);

    /**
     * If the factory was specified in the strategy, use that information to
     * create a converter.
     * @param ranges The ranges of the variables.
     * @param defaultRange The range of the variables not mentioned in ranges.
     * @return A converter using the specified factory, see implementation
     * of getPoloSatConverter using a factory as a parameter.
     */
    public PoloSatConverter getPoloSatConverter(
            final Map<String, BigInteger> ranges,
            final BigInteger defaultRange) {
        if (Globals.useAssertions) {
            assert (this.factoryCreator != null);
        }
        return this.getPoloSatConverter(
                this.factoryCreator.getFactory(), ranges, defaultRange);
    }

    protected PoloSatConfigInfo getPoloSatConfigInfo() {
        return new PoloSatConfigInfo(this.useIFFsInGT, this.gtMode,
                this.sumType, this.powersAsComb, this.newTimes,
                this.appendForTimes, this.tracking, this.productAbstraction,
                this.neqSearchstrict, this.useShifts, this.useBinaryShifts,
                this.useTimesTwoHardcoded, this.unaryMode, this.newUnaryPower,
                this.unaryIndefinites);
    }

    public static class Arguments {
        public boolean useTimesTwoHardcoded = false;
        public boolean appendForTimes = true;
        public FormulaFactoryCreator formulaFactory = new NonCountingCircuitFactoryCreator();
        public GTMode gtMode = GTMode.DEEP;
        public boolean neqSearchstrict = true;
        public boolean newTimes = true;
        public boolean powersAsComb = false;
        public boolean productAbstraction = false;
        public SumType sumType = SumType.MINIMAL;
        public boolean tracking = true;
        public boolean useIFFsInGT = true;
        public boolean useShifts = false;
        public boolean useBinaryShifts = true;
        public UNARY_MODE unaryMode = UNARY_MODE.SIDECONSTRAINTS;
        public boolean newUnaryPower = false;
        public boolean unaryIndefinites = false;
    }
}
