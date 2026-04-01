package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import immutables.*;

/**
 * Contains some detail configuration information that some PoloSatConverters
 * use for their configuration. Immutable, so instances can be passed around
 * without having to worry about external modifications.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class PoloSatConfigInfo implements Immutable {

    public enum UNARY_MODE  {
        SIDECONSTRAINTS,
        CIRCUIT
    }


    // true: use (A iff B); false: use (A and not B) inside GT encoding
    private final boolean useIFFsInGT;

    // there are several ways of encoding GT
    private final GTMode gtMode;

    // how do we encode n-ary sums?
    private final SumType sumType;

    // do we encode powers as combs? (if not, repeated binary squaring is used)
    private final boolean powersAsComb;

    // use "new" times encoding of 11/06?
    private final boolean newTimes;

    // use list appending for products instead of naive addition
    // where available?
    private final boolean appendForTimes;

    // keep track of intermediate results?
    private final boolean tracking;

    // perform product abstraction?
    private final boolean productAbstraction;

    // true:  searchstrict via not and(p_i = q_i)
    // false: searchstrict via or(p_i > q_i)
    private final boolean neqSearchstrict;

    // Use shifts instead of multiplication on specified variables?
    private final boolean useShifts;

    // If using shifts: Should they be represented unary?
    private final boolean binaryShifts;

    // Should times x (x <= 2) be treated in a special way?
    private final boolean timesTwoHardCoded;

    // How should unary shifting be encoded, esp. where should the limiting of search space occur?
    private final UNARY_MODE unaryMode;

    // Should we use the new power system for unary encoding?
    private final boolean newUnaryPower;

    // encode indefinites in unary?
    // (note: this parameter is unrelated to the above other parameters
    // with "unary" in their name; they are only relevant for the shift-based
    // encoding for powers of two)
    private final boolean unaryIndefinites;

    /**
     * @param useIFFsInGT - true: use (A iff B);
     *  false: use (A and not B) inside GT encoding
     * @param gtMode - there are several ways of encoding GT
     * @param sumType - how do we encode n-ary sums?
     * @param powersAsComb - do we encode powers as combs?
     *  (if not, repeated binary squaring is used)
     * @param appendForTimes - do we want to use append for times?
     */
    public PoloSatConfigInfo(final boolean useIFFsInGT, final GTMode gtMode,
            final SumType sumType, final boolean powersAsComb,
            final boolean newTimes, final boolean appendForTimes,
            final boolean tracking, final boolean productAbstraction,
            final boolean neqSearchstrict, final boolean useShifts, final boolean binaryShifts, final boolean timesTwoHardCoded,
            final UNARY_MODE unaryMode, final boolean newUnaryPower,
            final boolean unaryIndefinites) {
        this.useIFFsInGT = useIFFsInGT;
        this.gtMode = gtMode;
        this.sumType = sumType;
        this.powersAsComb = powersAsComb;
        this.newTimes = newTimes;
        this.appendForTimes = appendForTimes;
        this.tracking = tracking;
        this.productAbstraction = productAbstraction;
        this.neqSearchstrict = neqSearchstrict;
        this.useShifts = useShifts;
        this.binaryShifts = binaryShifts;
        this.timesTwoHardCoded = timesTwoHardCoded;
        this.unaryMode = unaryMode;
        this.newUnaryPower = newUnaryPower;
        this.unaryIndefinites = unaryIndefinites;
    }

    /**
     * If you are not sure how to set the options, just use this
     * constructor. Its default values should be a good starting point.
     */
    public PoloSatConfigInfo() {
        this.useIFFsInGT = true;
        this.gtMode = GTMode.DEEP;
        this.sumType = SumType.MINIMAL;
        this.powersAsComb = false;
        this.newTimes = true;
        this.appendForTimes = true;
        this.tracking = true;
        this.productAbstraction = false;
        this.neqSearchstrict = true;
        this.useShifts = false;
        this.binaryShifts = true;
        this.timesTwoHardCoded = false;
        this.unaryMode = UNARY_MODE.CIRCUIT;
        this.newUnaryPower = false;
        this.unaryIndefinites = false;
    }

    /**
     * @return Returns the gtMode.
     */
    public GTMode getGtMode() {
        return this.gtMode;
    }

    /**
     * @return Returns the newTimes.
     */
    public boolean getNewTimes() {
        return this.newTimes;
    }

    /**
     * @return the appendForTimes
     */
    public boolean getAppendForTimes() {
        return this.appendForTimes;
    }

    /**
     * @return Returns the tracking.
     */
    public boolean getTracking() {
        return this.tracking;
    }

    /**
     * @return the productAbstraction
     */
    public boolean getProductAbstraction() {
        return this.productAbstraction;
    }

    /**
     * @return Returns the powersAsComb.
     */
    public boolean getPowersAsComb() {
        return this.powersAsComb;
    }

    /**
     * @return Returns the sumType.
     */
    public SumType getSumType() {
        return this.sumType;
    }

    /**
     * @return Returns the useIFFsInGT.
     */
    public boolean getUseIFFsInGT() {
        return this.useIFFsInGT;
    }

    /**
     * @return Returns the neqSearchstrict.
     */
    public boolean getNeqSearchstrict() {
        return this.neqSearchstrict;
    }

    public boolean getUseShifts() {
        return this.useShifts;
    }

    public boolean getBinaryShifts() {
        return this.binaryShifts;
    }


    public boolean getTimesTwoHardCoded() {
        return this.timesTwoHardCoded;
    }

    public UNARY_MODE getUnaryMode() {
        return this.unaryMode;
    }

    public boolean getNewUnaryPower() {
        return this.newUnaryPower;
    }

    /**
     * @return the unaryIndefinites
     */
    public boolean getUnaryIndefinites() {
        return this.unaryIndefinites;
    }
}
