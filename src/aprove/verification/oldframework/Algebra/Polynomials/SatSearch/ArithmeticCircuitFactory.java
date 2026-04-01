package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Constructs some predefined Boolean circuits which denote that
 * some circuit node tuples are in certain relations (>, =, >=) or
 * which compute certain arithmetic functions over them (+, *).
 * Note that any List you pass to the methods will be incorporated
 * into the built circuits, so changing the lists or their
 * elements afterwards will change the circuits, too.
 *
 * They are modeled via the same classes that are used for
 * propositional formulae. The only difference between Boolean
 * circuits and formulae is that formulae have a
 * fan-out of at most one (tree style), whereas circuits permit
 * arbitrarily high fan-outs (directed acyclic graph). That way,
 * we can share common subexpressions and achieve a considerable
 * space reduction. Java conveniently allows such a representation
 * by subexpressions being referenced by more than just one node.
 *
 * Note: This class was previously known as PredefinedCircuitFactory.
 * Search for this name if you are interested in the
 * corresponding CVS history.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class ArithmeticCircuitFactory implements ArithmeticFactory {

    private final GTMode GT_MODE; // how to encode >

    private final boolean USE_GE_INSTEAD_OF_EQ_IN_GT; // >= or == in GT?
                                                      // (see def)

    private final boolean USE_NEW_TIMES; // use "new" times encoding of 11/06?

    private final boolean USE_APPEND_FOR_TIMES;

    private final boolean USE_SPECIAL_TIMES_TWO;

    private final boolean TRACKING;

    private final boolean BINARYSHIFTS; // Binary shifts prohibit certain things.

    private final FormulaFactory<None> formulaFactory;
    // used for building new circuits

    private final Constant<None> ZERO;
    // shall be used for the constant gates ZERO for circuits produced by this

    private final static Logger log = Logger.getLogger("ArithmeticCircuitFactory");

    protected ArithmeticCircuitFactory(final FormulaFactory<None> formulaFactory,
            final PoloSatConfigInfo config) {
        this.formulaFactory = formulaFactory;
        this.ZERO = this.formulaFactory.buildConstant(false);
        this.GT_MODE = config.getGtMode();
        this.USE_GE_INSTEAD_OF_EQ_IN_GT = ! config.getUseIFFsInGT();
        this.USE_NEW_TIMES = config.getNewTimes();
        this.USE_APPEND_FOR_TIMES = config.getAppendForTimes();
        this.TRACKING = config.getTracking();
        this.BINARYSHIFTS = config.getUseShifts() & config.getBinaryShifts();
        this.USE_SPECIAL_TIMES_TWO = config.getTimesTwoHardCoded();

    }

    /**
     * Creates a new ArithmeticCircuitFactory which uses circuitFactory to build
     * circuits.
     *
     * @param circuitFactory the FormulaFactory to be used
     * @param config
     * @return a new ArithmeticCircuitFactory
     */
    public static ArithmeticCircuitFactory create(final FormulaFactory<None> circuitFactory,
            final PoloSatConfigInfo config) {
        return new ArithmeticCircuitFactory(circuitFactory, config);
    }


    /* FIXME fix this docu
     * Small guide to understanding this class:
     * - The methods are based on certain circuits.
     *   You are assumed to have access to the corresponding document,
     *   otherwise understanding might require some reverse engineering of
     *   the circuits from the code (not too difficult, but nasty).
     * - The set of positions is assumed to be Nats^*,
     *   hence the first argument of a junctor at the root position is at
     *   position 0 (not 1!). This is for the sake of avoiding needless
     *   off by one errors.
     * - Let <p> \in Nats^*. Java variables named pos<p> are used to contain
     *   the circuit at position <p>. Variables named pos<p>0To<p>n
     *   are used to contain the arguments of the NaryJunctorFormula
     *   at position <p>.
     *   Note that in contrast to proper formulae (tree-like),
     *   a subcircuit may be referenced by more than one position
     *   in general. Still, we name the variables this way where suitable.
     * - By convention, input formula lists are called xs and ys.
     *   None of the lists may be empty.
     * - In case we return an output list, we call it zs.
     */

    /**
     * @param xs - the first factor
     * @param ys - the second factor
     * @return
     *  x - circuit for the product of xs and ys<br>
     *  y - the maximum value the product of xs and ys can assume
     */
    @Override
    public PolyCircuit buildTimesCircuit(final PolyCircuit xs, final PolyCircuit ys) {
        final List<Formula<None>> zs = this.buildTimesCircuit(xs.getFormulae(), ys.getFormulae(), xs.getMax(), ys.getMax());
        if (this.TRACKING) {
            final BigInteger zsMax = xs.getMax().multiply(ys.getMax());
            if (zsMax.signum() == 0) {
                final Formula<None> ff = this.formulaFactory.buildConstant(false);
                return new PolyCircuit(Collections.singletonList(ff), zsMax);
            }
            final int zsMaxLength = zsMax.bitLength();
            // Not applicable for binary shifts
            if (!this.BINARYSHIFTS) {
                for (int i = zs.size() - 1; i >= zsMaxLength; --i) {
                    zs.remove(i);
                }
            }
            return new PolyCircuit(zs, zsMax);
        }
        else {
            return new PolyCircuit(zs, BigInteger.ZERO);
        }
    }

    /**
     * @param xs - the first addend
     * @param ys - the second addend
     * @return
     *  x - circuit for the sum of xs and ys<br>
     *  y - the maximum value the sum of xs and ys can assume
     */
    @Override
    public PolyCircuit buildPlusCircuit(final PolyCircuit xs, final PolyCircuit ys) {
        final List<Formula<None>> zs = this.buildPlusCircuit(xs.getFormulae(), ys.getFormulae());
        if (this.TRACKING) {
            final BigInteger zsMax = xs.getMax().add(ys.getMax());
            if (zsMax.signum() == 0) {
                final Formula<None> ff = this.formulaFactory.buildConstant(false);
                return new PolyCircuit(Collections.singletonList(ff), zsMax);
            }
            final int zsMaxLength = zsMax.bitLength();
            if (!this.BINARYSHIFTS) {
                for (int i = zs.size() - 1; i >= zsMaxLength; --i) {
                    zs.remove(i);
                }
            }
            return new PolyCircuit(zs, zsMax);
        }
        else {
            return new PolyCircuit(zs, BigInteger.ZERO);
        }
    }

    /**
     * @param shiftBy - How many bits to shift? (UNARY value)
     * @param xs - the factor
     * @return
     *  x - circuit for the shift of xs << log(shiftBy)
     *  y - the maximum value the shift can assume
     */
    @Override
    public PolyCircuit buildShiftRightUnary(final PolyCircuit shiftBy, final PolyCircuit xs) {
        final List<Formula<None>> zs = this.buildShiftRightUnary(shiftBy.getFormulae(), xs.getFormulae());
        //DEBUG
        //final List<Formula<None>> zs = buildTimesCircuit(shiftBy.getFormulae(), xs.getFormulae());
        if (this.TRACKING) {
            final BigInteger zsMax = xs.getMax().multiply(shiftBy.getMax());
            if (zsMax.signum() == 0) {
                final Formula<None> ff = this.formulaFactory.buildConstant(false);
                return new PolyCircuit(Collections.singletonList(ff), zsMax);
            }
            final int zsMaxLength = zsMax.bitLength();
            if (!this.BINARYSHIFTS) {
                for (int i = zs.size() - 1; i >= zsMaxLength; --i) {
                    zs.remove(i);
                }
            }
            return new PolyCircuit(zs, zsMax);
        }
        else {
            return new PolyCircuit(zs, BigInteger.ZERO);
        }
    }

    /**
     * Internal function for shift right (unary version)
     * @param shiftBy
     * @param xs
     * @return
     */
    private List<Formula<None>> buildShiftRightUnary(final List<? extends Formula<None>> shiftBy, final List<? extends Formula<None>> xs) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! shiftBy.isEmpty());
        }


        int xsSize, sbSize;
        xsSize = xs.size();
        sbSize = shiftBy.size();

        // this may look more involved than it actually is ...
        // idea: do not perform plus for the positions where you
        // would always have ZERO in written multiplication
        final List<List<Formula<None>>> xAndYs = new ArrayList<List<Formula<None>>>(sbSize);

        // Cache ands between bits of xs and ys
        // Note that the and is represented by ys[0]&<xs> + ys[1]&(<xs> << 1) + ...
        // The stored lists are of the form ys[i]&<xs>
        for (int i = 0; i < sbSize; ++i) {
            final Formula<None> y = shiftBy.get(i);
            final List<Formula<None>> addendI = new ArrayList<Formula<None>>(xsSize);
            for (int j = 0; j < xsSize; ++j) {
                final Formula<None> x = xs.get(j);
                final Formula<None> xAndY = this.formulaFactory.buildAnd(y, x);
                addendI.add(xAndY);
            }
            xAndYs.add(addendI);
        }


        List<Formula<None>> currentSumTuple, result;
        result = new ArrayList<Formula<None>>(xsSize + sbSize);
        // First part: res = ys[0]&<xs>
        currentSumTuple = xAndYs.get(0);
        // The least-valued bit will not be added more times, finalize it
        result.add(currentSumTuple.get(0));
        // Shift our view of the list by one bit.
        currentSumTuple = currentSumTuple.subList(1, currentSumTuple.size());
        for (int i = 1; i < sbSize; ++i) {
            final List<Formula<None>> currentAddend = xAndYs.get(i);
            // Now we already have a prior bit there, so or the new entry to the old one
            // This is the only change to times in terms of logic!
            currentSumTuple = this.buildBitwiseOrCircuit(currentSumTuple, currentAddend);
            // The least-valued bit will not change anymore...
            result.add(currentSumTuple.get(0));
            // ...and shift.
            currentSumTuple = currentSumTuple.subList(1, currentSumTuple.size());
        }
        // add all remaining bits to the result (those which would still change were there more bits in the ys)
        result.addAll(currentSumTuple);
        return result;

    }


    /**
     * Helper method to build xs | ys
     * @param xs
     * @param ys
     * @return
     */
    private List<Formula<None>> buildBitwiseOrCircuit(final List<Formula<None>> xs,
        final List<Formula<None>> ys) {

        //log.log(Level.FINER, "Bitwise or of " + xs.toString() + " - " + ys.toString());

        final int maxIndex = xs.size() > ys.size() ? xs.size() : ys.size();

        final List<Formula<None>> result = new ArrayList<Formula<None>>(maxIndex);

        for (int i = 0; i < maxIndex; i++) {
            if ((xs.size() > i) && (ys.size() > i)) {
                result.add(this.formulaFactory.buildOr(xs.get(i), ys.get(i)));
            } else if (xs.size() > i) {
                result.add(xs.get(i));
            } else if (ys.size() > i) {
                result.add(ys.get(i));
            } else {
                // this should never happen
                if (Globals.useAssertions) {assert false;}
            }
            //log.log(Level.FINER,result.toString());
        }

        return result;
    }


    @Override
    public PolyCircuit buildMixedDualAdder(PolyCircuit xs,
            PolyCircuit bs) {
        final List<Formula<None>> zs = this.buildMixDualAdderCircuit(xs.getFormulae(), bs.getFormulae());
        //DEBUG
        //final List<Formula<None>> zs = buildTimesCircuit(shiftBy.getFormulae(), xs.getFormulae());
        if (this.TRACKING) {
            final BigInteger zsMax = xs.getMax().add(bs.getMax());
            if (zsMax.signum() == 0) {
                final Formula<None> ff = this.formulaFactory.buildConstant(false);
                return new PolyCircuit(Collections.singletonList(ff), zsMax);
            }
            final int zsMaxLength = zsMax.bitLength();
            for (int i = zs.size() - 1; i >= zsMaxLength; --i) {
                zs.remove(i);
            }
            return new PolyCircuit(zs, zsMax);
        }
        else {
            return new PolyCircuit(zs, BigInteger.ZERO);
        }
    }

    /**
     * Build a circuit of a Mixed-Dual-Adder.
     * B can only be a power of two or zero for this to be correct; this needs to be ensured elsewhere!
     * @param xs
     * @param bs
     * @param rangeOfX
     * @param rangeOfB
     * @return
     */
    private List<Formula<None>> buildMixDualAdderCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> bs) {

        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! bs.isEmpty());
        }

        List<Formula<None>> zs;
        zs = new ArrayList<Formula<None>>(xs.size() >= bs.size() ? xs.size()+1 : bs.size() /* No +1 needed, see theory */);

        int size = xs.size(); // Only x part relevant.


        final List<Formula<None>> x0b0 = new ArrayList<Formula<None>>(2);
        x0b0.add(xs.get(0));
        x0b0.add(bs.get(0));
        // needed for the 1st element of zs



        // First bit: Well, we do have an XOr here.
        Formula<None> z0;
        z0 = this.formulaFactory.buildXor(x0b0);
        Formula<None> zI;
        FormulaFactory<None> ff = this.formulaFactory;

        zs.add(z0);
        for (int i = 1; i < size; ++i) {

            // Still enough b's?
            if (bs.size() > i) {

                // The encoding is:
                // x[i] & -b[i] & (z[i-1] | -x[i-1]) /* there has not been a carry, there will not be, and we have a bit set */
                // | -x[i] & (b[i] /* there is the dual bit set at this point without producing a carry */ | x[i-1] & -z[i-1] /* There was a carry and we can resolve it */
                zI = ff.buildOr(
                        ff.buildAnd(xs.get(i), ff.buildNot(bs.get(i)),
                                ff.buildOr(zs.get(i-1), ff.buildNot(xs.get(i-1)))),
                        ff.buildAnd(ff.buildNot(xs.get(i)),
                                ff.buildOr(bs.get(i),
                                    ff.buildAnd(xs.get(i-1), ff.buildNot(zs.get(i-1))))));

            } else {
                // We're out of b's, but still have x's. Just replace b[i] by false in the above and simplify.
                zI = ff.buildOr(
                        ff.buildAnd(xs.get(i),
                                ff.buildOr(zs.get(i-1), ff.buildNot(xs.get(i-1)))),
                        ff.buildAnd(ff.buildNot(xs.get(i)),
                                ff.buildAnd(xs.get(i-1), ff.buildNot(zs.get(i-1)))));
            }

            zs.add(zI);
        }

        // We are out of x's.
        // One more carry can occur, and maybe we still have b's; simplify x[i] = false in the above:
        if (bs.size() > size) {
            zI = ff.buildOr(bs.get(size),
                            ff.buildAnd(xs.get(size-1), ff.buildNot(zs.get(size-1))));
        } else {
            // No more b's, no more x's. Just calculate the last carry.
            zI = ff.buildAnd(xs.get(size-1), ff.buildNot(zs.get(size-1)));
        }
        zs.add(zI);

        // From here on it could still be that there are bs left, but no xs.
        // In this case there will not be any carries to disturb: either a dual entry was set in the lower ranges - thatone will have carried out by this position.
        // Or it has not - then it will have nothing with which it could lead to a carry.
        // So just propagate the bi's.
        int bSize = bs.size();
        for (int i = size + 1; i < bSize /* No extra bit */; i++) {
            zI = bs.get(i);
            zs.add(zI);
        }




        if (Globals.useAssertions) {
            assert zs.size() >= 1 + xs.size();
        }

        //cropList(zs); // No messy ZEROs.

        return zs;

    }



    /**
     * Builds a circuit that has xs * ys as output, given xs and ys
     * as inputs.
     *
     * @param xs the first addend
     * @param ys ths second addend
     * @return output of a circuit that encodes xs * ys given xs and
     *  ys as inputs
     */
    private List<Formula<None>> buildTimesCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys, BigInteger rangeOfX, BigInteger rangeOfY) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        // just consider the case that xs.size() >= ys.size(),
        // times is commutative :)
        if (xs.size() < ys.size()) {
            final List<? extends Formula<None>> tmp = xs;
            xs = ys;
            ys = tmp;
            final BigInteger tmp2 = rangeOfX;
            rangeOfX = rangeOfY;
            rangeOfY = tmp2;
        }

        int xsSize, ysSize;
        xsSize = xs.size();
        ysSize = ys.size();

        if (this.USE_NEW_TIMES) {
            if (this.USE_APPEND_FOR_TIMES) {

                // From the old code: Catch case that times is applied to a factor <= 3.
                if (this.USE_SPECIAL_TIMES_TWO && (rangeOfY == BigInteger.valueOf(2))) {
                    final int zsSize = xsSize + ysSize;
                    List<Formula<None>> zs; // to be returned
                    zs = new ArrayList<Formula<None>>(zsSize);
                    final List<Formula<None>> zeroThenXs = new ArrayList<Formula<None>>(xsSize+1);
                    zeroThenXs.add(this.ZERO);
                    zeroThenXs.addAll(xs);

                    List<Formula<None>> sum; // result iff ys.get(0)==ys.get(1)==ONE
                    sum = this.buildPlusCircuit(xs, zeroThenXs);

                    // avoid redundant method calls
                    Formula<None> ys0, ys1, notYs0, notYs1;
                    ys0 = ys.get(0);
                    ys1 = ys.get(1);
                    notYs0 = this.formulaFactory.buildNot(ys0);
                    notYs1 = this.formulaFactory.buildNot(ys1);

                    // now define the result
                    final Formula<None> z0 = this.formulaFactory.buildAnd(ys0, xs.get(0));
                    zs.add(z0);
                    for (int i = 1; i < xsSize; ++i) {
                        Formula<None> pos0, pos1, pos2, zI;
                        pos0 = this.formulaFactory.buildAnd(ys0, ys1, sum.get(i)); // ys == 3
                        pos1 = this.formulaFactory.buildAnd(ys0, notYs1, xs.get(i)); // ys == 1
                        pos2 = this.formulaFactory.buildAnd(notYs0, ys1, xs.get(i-1)); // ys == 2

                        // either one of the above cases for ys holds or implicit
                        // disjunct ZERO for the case ys == 0 will result
                        zI = this.formulaFactory.buildOr(pos0, pos1, pos2);
                        zs.add(zI);
                    }

                    {
                        Formula<None> pos0, pos1, zXsSize;
                        pos0 = this.formulaFactory.buildAnd(ys0, ys1, sum.get(xsSize)); // ys == 3
                        pos1 = this.formulaFactory.buildAnd(notYs0, ys1, xs.get(xsSize-1)); // ys == 2
                        zXsSize = this.formulaFactory.buildOr(pos0, pos1);
                        zs.add(zXsSize);
                    }

                    {
                        Formula<None> zXsSizePlusOne;
                        zXsSizePlusOne = this.formulaFactory.buildAnd(ys0, ys1, sum.get(xsSize+1));
                        zs.add(zXsSizePlusOne);
                    }
                    return zs;

                }
                // this may look more involved than it actually is ...
                // idea: do not perform plus for the positions where you
                // would always have ZERO in written multiplication
                final List<List<Formula<None>>> xAndYs = new ArrayList<List<Formula<None>>>(ysSize);

                // Cache ands between bits of xs and ys
                // Note that the and is represented by ys[0]&<xs> + ys[1]&(<xs> << 1) + ...
                // The stored lists are of the form ys[i]&<xs>
                for (int i = 0; i < ysSize; ++i) {
                    final Formula<None> y = ys.get(i);
                    final List<Formula<None>> addendI = new ArrayList<Formula<None>>(xsSize);
                    for (int j = 0; j < xsSize; ++j) {
                        final Formula<None> x = xs.get(j);
                        final Formula<None> xAndY = this.formulaFactory.buildAnd(y, x);
                        addendI.add(xAndY);
                    }
                    xAndYs.add(addendI);
                }


                List<Formula<None>> currentSumTuple, result;
                result = new ArrayList<Formula<None>>(xsSize + ysSize);
                // First part: res = ys[0]&<xs>
                currentSumTuple = xAndYs.get(0);
                // The least-valued bit will not be added more times, finalize it
                result.add(currentSumTuple.get(0));
                // Shift our view of the list by one bit.
                currentSumTuple = currentSumTuple.subList(1, currentSumTuple.size());
                for (int i = 1; i < ysSize; ++i) {
                    final List<Formula<None>> currentAddend = xAndYs.get(i);
                    // Now we already have a prior bit there, so add the new entry to the old one.
                    currentSumTuple = this.buildPlusCircuit(currentSumTuple, currentAddend);
                    // The least-valued bit will not change anymore...
                    result.add(currentSumTuple.get(0));
                    // ...and shift.
                    currentSumTuple = currentSumTuple.subList(1, currentSumTuple.size());
                }
                // add all remaining bits to the result (those which would still change were there more bits in the ys)
                result.addAll(currentSumTuple);
                return result;
            }
            else {
                List<List<Formula<None>>> addendList;
                addendList = new ArrayList<List<Formula<None>>>(ysSize);

                for (int i = 0; i < ysSize; ++i) {
                    final List<Formula<None>> addendI = new ArrayList<Formula<None>>(xsSize+i);
                    for (int j = 0; j < i; ++j) {
                        addendI.add(this.ZERO);
                    }
                    addendList.add(addendI);
                }
                // build the addends-to-be and pad them with i ZEROs

                // now insert the suitable conjunctions of y_i and x_j
                for (int i = 0; i < ysSize; ++i) {
                    final Formula<None> y = ys.get(i);
                    final List<Formula<None>> addendI = addendList.get(i);
                    for (final Formula<None> x : xs) {
                        final Formula<None> xAndY = this.formulaFactory.buildAnd(y, x);
                        addendI.add(xAndY);
                    }
                }

                // now to the actual addition circuits (action!)
                List<Formula<None>> currentSum = addendList.get(0);
                for (int i = 1; i < ysSize; ++i) {
                    currentSum = this.buildPlusCircuit(currentSum, addendList.get(i));
                }
                return currentSum;
            }
        }
        else {
            final int zsSize = xsSize + ysSize;
            List<Formula<None>> zs; // to be returned
            zs = new ArrayList<Formula<None>>(zsSize);

            // now we get 3 cases:
            switch (ysSize) {
            case 1: {
                final Formula<None> ys0 = ys.get(0);
                for (int i = 0; i < xsSize; ++i) {
                    final Formula<None> zI = this.formulaFactory.buildAnd(ys0, xs.get(i));
                    zs.add(zI);
                }
                zs.add(this.ZERO); // zs has arity xsSize+1 just for the sake of consistency
                                   // TODO Can we omit that ZERO element?
                                   //      The circuits on the next level do not
                                   //      need it anyway.
                break;
            }
            case 2: {
                final List<Formula<None>> zeroThenXs = new ArrayList<Formula<None>>(xsSize+1);
                zeroThenXs.add(this.ZERO);
                zeroThenXs.addAll(xs);

                List<Formula<None>> sum; // result iff ys.get(0)==ys.get(1)==ONE
                sum = this.buildPlusCircuit(xs, zeroThenXs);

                // avoid redundant method calls
                Formula<None> ys0, ys1, notYs0, notYs1;
                ys0 = ys.get(0);
                ys1 = ys.get(1);
                notYs0 = this.formulaFactory.buildNot(ys0);
                notYs1 = this.formulaFactory.buildNot(ys1);

                // now define the result
                final Formula<None> z0 = this.formulaFactory.buildAnd(ys0, xs.get(0));
                zs.add(z0);
                for (int i = 1; i < xsSize; ++i) {
                    Formula<None> pos0, pos1, pos2, zI;
                    pos0 = this.formulaFactory.buildAnd(ys0, ys1, sum.get(i)); // ys == 3
                    pos1 = this.formulaFactory.buildAnd(ys0, notYs1, xs.get(i)); // ys == 1
                    pos2 = this.formulaFactory.buildAnd(notYs0, ys1, xs.get(i-1)); // ys == 2

                    // either one of the above cases for ys holds or implicit
                    // disjunct ZERO for the case ys == 0 will result
                    zI = this.formulaFactory.buildOr(pos0, pos1, pos2);
                    zs.add(zI);
                }

                {
                    Formula<None> pos0, pos1, zXsSize;
                    pos0 = this.formulaFactory.buildAnd(ys0, ys1, sum.get(xsSize)); // ys == 3
                    pos1 = this.formulaFactory.buildAnd(notYs0, ys1, xs.get(xsSize-1)); // ys == 2
                    zXsSize = this.formulaFactory.buildOr(pos0, pos1);
                    zs.add(zXsSize);
                }

                {
                    Formula<None> zXsSizePlusOne;
                    zXsSizePlusOne = this.formulaFactory.buildAnd(ys0, ys1, sum.get(xsSize+1));
                    zs.add(zXsSizePlusOne);
                }
                break;
            }
            default: // ysSize > 2
                List<List<Formula<None>>> realSums;
                // contains the *actual* intermediate sums (currently called V)

                List<List<Formula<None>>> estimatedSums;
                // contains the intermediate sums that might occur
                // if y_(i+1) is true (currently called T)

                realSums = new ArrayList<List<Formula<None>>>(ysSize-2);
                estimatedSums = new ArrayList<List<Formula<None>>>(ysSize-2);

                // first define the real and the estimated sums,
                // they depend on each other
                final List<Formula<None>> ys01 = new ArrayList<Formula<None>>(2);
                ys01.add(ys.get(0));
                ys01.add(ys.get(1));

                List<Formula<None>> realSumI = this.buildTimesCircuit(xs, ys01, rangeOfX, rangeOfY); // we do not want to enter the special case, so leave rangeOfY.
                realSums.add(realSumI);

                // needed for estimatedSumsI
                final List<Formula<None>> twoZerosThenXs = new ArrayList<Formula<None>>(xsSize + 2);
                twoZerosThenXs.add(this.ZERO);
                twoZerosThenXs.add(this.ZERO);
                twoZerosThenXs.addAll(xs);

                List<Formula<None>> estimatedSumI = this.buildPlusCircuit(realSumI, twoZerosThenXs);
                estimatedSums.add(estimatedSumI);

                List<Formula<None>> prevRealSum = realSumI;

                for (int i = 1; i < ysSize - 2; ++i) {
                    Formula<None> ysIplus1, notYsIplus1;
                    ysIplus1 = ys.get(i+1);
                    notYsIplus1 = this.formulaFactory.buildNot(ysIplus1);

                    // first build realSumI
                    realSumI = new ArrayList<Formula<None>>(xsSize + i + 1);
                    for (int j = 0; j < xsSize + i + 1; ++j) {
                        Formula<None> pos0, pos1, realSumIJ;
                        pos0 = this.formulaFactory.buildAnd(ysIplus1, estimatedSumI.get(j));
                        // estimatedSumI stems from the previous
                        // iteration of the outer loop!

                        pos1 = this.formulaFactory.buildAnd(notYsIplus1, prevRealSum.get(j));
                        realSumIJ = this.formulaFactory.buildOr(pos0, pos1);
                        realSumI.add(realSumIJ);
                    }
                    final Formula<None> realSumILast = this.formulaFactory.buildAnd(ysIplus1,
                            estimatedSumI.get(xsSize + i + 1));
                            // estimatedSumI from previous iteration
                    realSumI.add(realSumILast);

                    prevRealSum = realSumI; // for the next iteration

                    // needed for next estimatedSumI
                    List<Formula<None>> iPlusTwoZerosXs;
                    iPlusTwoZerosXs = new ArrayList<Formula<None>>(i + 2 + xsSize);
                    for (int k = 0; k < i + 2; ++k) {
                        iPlusTwoZerosXs.add(this.ZERO);
                    }
                    iPlusTwoZerosXs.addAll(xs);

                    // are we using the indices on iPlusOneZerosXs correctly?
                    if (Globals.useAssertions) {
                        for (int j = 0; j < i + 2; ++j) {
                            assert iPlusTwoZerosXs.get(j) == this.ZERO;
                        }
                        final Formula<None> firstX = iPlusTwoZerosXs.get(i+2);
                        assert firstX == xs.get(0);
                    }

                    estimatedSumI = this.buildPlusCircuit(realSumI, iPlusTwoZerosXs);

                    // add the freshly computed sums to their lists
                    realSums.add(realSumI);
                    estimatedSums.add(estimatedSumI);
                }

                // now to the actual result zs
                Formula<None> ysLastOne, notYsLastOne;
                List<Formula<None>> estimatedSumsLastOne, realSumsLastOne;

                ysLastOne = ys.get(ysSize - 1);
                notYsLastOne = this.formulaFactory.buildNot(ysLastOne);
                estimatedSumsLastOne = estimatedSums.get(ysSize - 3);
                realSumsLastOne = realSums.get(ysSize - 3);

                if (Globals.useAssertions) {
                    assert estimatedSums.size() == ysSize - 2;
                    assert realSums.size() == ysSize - 2;
                    assert estimatedSumsLastOne.size() == zsSize;
                }

                for (int i = 0; i < zsSize - 1; ++i) {
                    Formula<None> pos0, pos1, zI;
                    pos0 = this.formulaFactory.buildAnd(ysLastOne, estimatedSumsLastOne.get(i));
                    pos1 = this.formulaFactory.buildAnd(notYsLastOne, realSumsLastOne.get(i));
                    zI = this.formulaFactory.buildOr(pos0, pos1);
                    zs.add(zI);
                }
                Formula<None> zLast;
                zLast = this.formulaFactory.buildAnd(ysLastOne,
                        estimatedSumsLastOne.get(zsSize - 1));
                zs.add(zLast);
            }

            if (Globals.useAssertions) {
                assert xs.size() + ys.size() == zs.size();
                assert zsSize == zs.size();
            }

            //cropList(zs);

            return zs;
        }
    }

    /**
     * Builds a circuit that has xs + ys as output, given xs and ys
     * as inputs.
     *
     * @param xs the first addend
     * @param ys ths second addend
     * @return output of a circuit that encodes xs + ys given xs and
     *  ys as inputs
     */
    private List<Formula<None>> buildPlusCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        List<Formula<None>> zs;
        zs = new ArrayList<Formula<None>>(xs.size() > ys.size() ? xs.size()+1 : ys.size()+1);

        // 3 cases:
        // 1) xs.size() == ys.size(), xs.size() == 1
        if (xs.size() == ys.size()) {
            final int size = xs.size();
            if (size == 1) {
                final List<Formula<None>> x0y0 = new ArrayList<Formula<None>>(2);
                x0y0.add(xs.get(0));
                x0y0.add(ys.get(0));
                Formula<None> z0, z1;
                z0 = this.formulaFactory.buildXor(x0y0);
                z1 = this.formulaFactory.buildAnd(x0y0); // share and enjoy.
                zs.add(z0);
                zs.add(z1);
            }
            else { // 2) xs.size() == ys.size() && xs.size() > 1
                final Formula<None>[] carries = new Formula[size-1];
                final List<Formula<None>> x0y0 = new ArrayList<Formula<None>>(2);
                x0y0.add(xs.get(0));
                x0y0.add(ys.get(0));
                // needed both for the 1st element of zs and of carries

                // first define all the carries
                carries[0] = this.formulaFactory.buildAnd(x0y0);
                for (int i = 1; i < carries.length; ++i) {
                    carries[i] = this.build2or3Circuit(xs.get(i),
                            ys.get(i), carries[i-1]);
                }

                // then the result based on xs, ys and carries
                Formula<None> z0;
                z0 = this.formulaFactory.buildXor(x0y0);
                zs.add(z0);
                for (int i = 1; i < size; ++i) {
                    Formula<None> zI;
                    zI = this.formulaFactory.buildXor(xs.get(i), ys.get(i), carries[i-1]);
                    zs.add(zI);
                }
                final Formula<None> zLast = this.build2or3Circuit(xs.get(size-1),
                        ys.get(size-1), carries[size-2]);
                zs.add(zLast);
            }
        }
        else {
            // 3) xs.size != ys.size()
            //    we only want to handle xs.size() < ys.size(),
            //    plus is commutative :)
            if (xs.size() > ys.size()) {
                // swap them
                final List<? extends Formula<None>> tmp = xs;
                xs = ys;
                ys = tmp;
            }

            int xsSize, ysSize;
            xsSize = xs.size();
            ysSize = ys.size();

            final Formula<None>[] carries = new Formula[ysSize-1];
            final List<Formula<None>> x0y0 = new ArrayList<Formula<None>>(2);
            x0y0.add(xs.get(0));
            x0y0.add(ys.get(0));
            // needed both for the 1st element of zs and of carries

            // first define all the carries
            carries[0] = this.formulaFactory.buildAnd(x0y0);
            for (int i = 1; i < xsSize; ++i) {
                carries[i] = this.build2or3Circuit(xs.get(i),
                        ys.get(i), carries[i-1]);
            }
            for (int i = xsSize; i < carries.length; ++i) {
                carries[i] = this.formulaFactory.buildAnd(ys.get(i), carries[i-1]);
            }

            // then define the result based on xs, ys and carries
            zs.add(this.formulaFactory.buildXor(x0y0));
            for (int i = 1; i < xsSize; ++i) {
                zs.add(this.formulaFactory.buildXor(xs.get(i), ys.get(i), carries[i-1]));
            }
            for (int i = xsSize; i < ysSize; ++i) {
                zs.add(this.formulaFactory.buildXor(ys.get(i), carries[i-1]));
            }
            final Formula<None> zLast = this.formulaFactory.buildAnd(ys.get(ysSize-1), carries[ysSize-2]);
            zs.add(zLast);
        }

        if (Globals.useAssertions) {
            assert zs.size() == 1 + Math.max(xs.size(), ys.size());
        }

        //cropList(zs); // No messy ZEROs.

        return zs;
    }

    /**
     * @param f1
     * @param f2
     * @param f3
     * @return a formula/circuit which is satisfied by exactly those
     *  interpretations that satisfy at least 2 of the arguments
     */
    public Formula<None> build2or3Circuit(final Formula<None> f1, final Formula<None> f2, final Formula<None> f3) {
        Formula<None> pos0, pos1, pos2;
        pos0 = this.formulaFactory.buildOr(f1, f2);
        pos1 = this.formulaFactory.buildOr(f1, f3);
        pos2 = this.formulaFactory.buildOr(f2, f3);
        return this.formulaFactory.buildAnd(pos0, pos1, pos2);
    }

    /**
     * Builds a Boolean circuit that encodes that xs
     * represents a strictly greater number than ys.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return a formula that encodes that xs > ys
     */
    @Override
    public Formula<None> buildGTCircuit(final List<? extends Formula<None>> xs,
            final List<? extends Formula<None>> ys) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        final int xsSize = xs.size();
        final int ysSize = ys.size();

        switch (this.GT_MODE) {
        case DEEP: {
            // Codish style.
            Formula<None> result;
            if (xsSize == 1 && ysSize == 1) {
                result = this.formulaFactory.buildAnd(xs.get(0),
                        this.formulaFactory.buildNot(ys.get(0)));
            }
            else if (xsSize > ysSize) {
                final List<Formula<None>> args = new ArrayList<Formula<None>>(1+xsSize-ysSize);
                for (int i = ysSize; i < xsSize; ++i) {
                    args.add(xs.get(i));
                }
                final List<Formula<None>> newXs = new ArrayList<Formula<None>>(ysSize);
                for (int i = 0; i < ysSize; ++i) {
                    newXs.add(xs.get(i));
                }
                args.add(this.buildGTCircuit(/*xs.subList(0, ysSize)*/newXs, ys));
                result = this.formulaFactory.buildOr(args);
            }
            else if (xsSize < ysSize) {
                final List<Formula<None>> args = new ArrayList<Formula<None>>(1+ysSize-xsSize);
                for (int i = xsSize; i < ysSize; ++i) {
                    args.add(this.formulaFactory.buildNot(ys.get(i)));
                }
                final List<Formula<None>> newYs = new ArrayList<Formula<None>>(xsSize);
                for (int i = 0; i < xsSize; ++i) {
                    newYs.add(ys.get(i));
                }
                args.add(this.buildGTCircuit(xs, /*ys.subList(0, xsSize)*/newYs));
                result = this.formulaFactory.buildAnd(args);
            }
            else { // xsSize == ysSize, xsSize != 1
                final Formula<None> lastX = xs.get(xsSize - 1);
                final Formula<None> lastY = ys.get(ysSize - 1);
                final Formula<None> leftDisjunct = this.formulaFactory.buildAnd(lastX,
                        this.formulaFactory.buildNot(lastY));

                Formula<None> eqConjunct;
                if (this.USE_GE_INSTEAD_OF_EQ_IN_GT) {
                    eqConjunct = this.formulaFactory.buildOr(lastX,
                            this.formulaFactory.buildNot(lastY));
                }
                else {
                    eqConjunct = this.formulaFactory.buildIff(lastX, lastY);
                }
                List<Formula<None>> newXs, newYs;
                newXs = new ArrayList<Formula<None>>(xsSize-1);
                newYs = new ArrayList<Formula<None>>(xsSize-1);
                for (int i = 0; i < xsSize - 1; ++i) {
                    newXs.add(xs.get(i));
                    newYs.add(ys.get(i));
                }
                final Formula<None> recursivelyBuiltConjunct = this.buildGTCircuit(/*xs.subList(0, xsSize-1)*/newXs, /*ys.subList(0, ysSize-1)*/newYs);
                final Formula<None> rightDisjunct = this.formulaFactory.buildAnd(eqConjunct, recursivelyBuiltConjunct);
                result = this.formulaFactory.buildOr(leftDisjunct, rightDisjunct);
            }
            return result;
        }
        case FLAT: { // flat style, but there are O(n^2) pointers
                     // to some (g)eqs involved.
            // The construction of the > circuit is not quite symmetric.
            // We need to distinguish between |xs| < |ys| and |xs| >= |ys|.
            final boolean xsSizeLTysSize = xsSize < ysSize;
            final int minSize = xsSizeLTysSize ? xsSize : ysSize;

            // Common feature: We will have a subcircuit which encodes that for
            // minSize, the numbers that correspond to the prefixes
            // of xs and ys of length minSize are in relation >.
            Formula<None> minSizeGT;
            List<Formula<None>> ppos0ToN; // args of minSizeGT

            {
                // eqs contains the formulae that encode that
                // xs.get(i) <-> ys.get(i) *in descending order of i*.
                // Note that xs.get(0) <-> ys.get(0) is never needed.
                // Hence, we do not include it in iffs.
                List<Formula<None>> eqs;
                eqs = new ArrayList<Formula<None>>(minSize - 1);
                for (int i = minSize - 1; i > 0; --i) {
                    Formula<None> currentEq;
                    if (this.USE_GE_INSTEAD_OF_EQ_IN_GT) {
                        currentEq = this.formulaFactory.buildOr(xs.get(i),
                                this.formulaFactory.buildNot(ys.get(i)));
                    }
                    else {
                        currentEq = this.formulaFactory.buildIff(xs.get(i), ys.get(i));
                    }
                    eqs.add(currentEq);
                }

                ppos0ToN = new ArrayList<Formula<None>>(minSize);

                for (int i = minSize - 1; i >= 0; --i) {
                    Formula<None> xsiGTysi;
                    xsiGTysi = this.formulaFactory.buildAnd(xs.get(i),
                            this.formulaFactory.buildNot(ys.get(i)));

                    List<Formula<None>> pposI0ToIP;
                    pposI0ToIP = new ArrayList<Formula<None>>(minSize - i);

                    // xs.get(i) > ys.get(i)
                    pposI0ToIP.add(xsiGTysi);

                    // for all k > i: xs.get(k) = ys.get(k)
                    for (int j = 0; j < (minSize - 1) - i; ++j) {
                        pposI0ToIP.add(eqs.get(j));
                    }

                    final Formula<None> disjunctI = this.formulaFactory.buildAnd(pposI0ToIP);
                    ppos0ToN.add(disjunctI);
                }

                minSizeGT = this.formulaFactory.buildOr(ppos0ToN);
            }

            if (xsSize == ysSize) {
                return minSizeGT;
            }
            else if (xsSizeLTysSize) {
                List<Formula<None>> args;
                args = new ArrayList<Formula<None>>(ysSize - xsSize + 1);
                for (int i = xsSize; i < ysSize; ++i) {
                    final Formula<None> negatedArg = this.formulaFactory.buildNot(ys.get(i));
                    args.add(negatedArg);
                }
                args.add(minSizeGT);
                final Formula<None> result = this.formulaFactory.buildAnd(args);
                return result;
            }
            else { // xsSize > ysSize
                List<Formula<None>> args;
                args = new ArrayList<Formula<None>>(ysSize);
                for (int i = ysSize; i < xsSize; ++i) {
                    args.add(xs.get(i));
                }
                args.addAll(ppos0ToN); // add all args of minSizeGT, too
                final Formula<None> result = this.formulaFactory.buildOr(args);
                return result;
            }
        }
        case LPO_LIKE: {
            final boolean xsSizeLTysSize = xsSize < ysSize;
            final int minSize = xsSizeLTysSize ? xsSize : ysSize;

            /* This is a try to encode > as in LPO. */
            // There are a few constraints.
            // If the terms are of equal length, go ahead as in LPO.
            // If x is longer, check whether there is any one in the more significant part. If so -> Done.
            //   If not -> Usual way.
            // If y is longer, check whether there is any one in the more significant part, if so -> Fail.
            //   If not -> Usual way.
            // Truth Variable for the whole construct.
            final Variable<None> isGT = this.formulaFactory.buildVariable();
            final Formula<None> notIsGT = this.formulaFactory.buildNot(isGT);
            List<Formula<None>> cnfConjuncts;
            cnfConjuncts = new ArrayList<Formula<None>>(6*minSize+3*Math.max(xsSize, ysSize)+3);

            // Introduce single atoms for each position. Enables us to use CNF directly.
            // Inside the loop, these are the v's.
            // They are mapped to the real formulas representing that bit.
            // Some DimacsCreators will respect this CNF w/o sending it through
            // the Tseitin transformation.

            cnfConjuncts.add(isGT);

            Variable<None> commonMatch = null;
            Formula<None> notCommonMatch = null;
            Variable<None> commonMatchPrevious = null;
            Formula<None> notCommonMatchPrevious = null;
            // The common part.
            for (int j = 0; j < minSize; ++j) {
                Formula<None> xsJ, notXsJ, ysJ, notYsJ;
                xsJ = xs.get(j);
                notXsJ = this.formulaFactory.buildNot(xsJ);
                ysJ = ys.get(j);
                notYsJ = this.formulaFactory.buildNot(ysJ);

                commonMatch = this.formulaFactory.buildVariable();
                notCommonMatch = this.formulaFactory.buildNot(commonMatch);

                // We have a match if Xj is set, but Yj is not.
                cnfConjuncts.add(this.formulaFactory.buildOr(commonMatch, notXsJ, ysJ));
                // We don't have a match (anymore) if Xj is unset and Yj is set.
                cnfConjuncts.add(this.formulaFactory.buildOr(notCommonMatch, xsJ, notYsJ));
                // If Xj is equal to Yj, keep match.
                // But we don't have a match if neither we had one nor Xj is set. Same with Yj
                if (j > 0) {
                    cnfConjuncts.add(this.formulaFactory.buildOr(commonMatch, notCommonMatchPrevious, notXsJ));
                    cnfConjuncts.add(this.formulaFactory.buildOr(notCommonMatch, commonMatchPrevious, xsJ));
                    cnfConjuncts.add(this.formulaFactory.buildOr(commonMatch, notCommonMatchPrevious, ysJ));
                    cnfConjuncts.add(this.formulaFactory.buildOr(notCommonMatch, commonMatchPrevious, notYsJ));
                }
                else {
                    cnfConjuncts.add(this.formulaFactory.buildOr(notCommonMatch, notYsJ));
                    cnfConjuncts.add(this.formulaFactory.buildOr(notCommonMatch, xsJ));
                }

                commonMatchPrevious = commonMatch;
                notCommonMatchPrevious = notCommonMatch;
            }

            if (xsSizeLTysSize) {
                // The Y is longer part.
                for (int i = minSize; i < ysSize; i++) {
                    // Yi set? Prohibit match!
                    cnfConjuncts.add(this.formulaFactory.buildNot(ys.get(i)));
                }
                // For testing on a match: commonMatch must have happened.
                cnfConjuncts.add(this.formulaFactory.buildOr(notIsGT, commonMatch));
                // And that is enough.
                cnfConjuncts.add(this.formulaFactory.buildOr(isGT, notCommonMatch));
            }
            else if (xsSize > ysSize) {
                // The X is longer part.
                // overlapMatch is the truth variable for the current binary digit.
                Variable<None> overlapMatch = null;
                Formula<None> notOverlapMatch = null;
                Variable<None> overlapMatchPrevious = null;
                Formula<None> notOverlapMatchPrevious = null;
                for (int i = minSize; i < xsSize; ++i) {
                    final Formula<None> xsI = xs.get(i);
                    final Formula<None> notXsI = this.formulaFactory.buildNot(xsI);

                    overlapMatch = this.formulaFactory.buildVariable();
                    notOverlapMatch = this.formulaFactory.buildNot(overlapMatch);
                    // No Xi? Keep match if there was one.
                    if (notOverlapMatchPrevious != null) {
                        cnfConjuncts.add(this.formulaFactory.buildOr(overlapMatch, notOverlapMatchPrevious));
                    }
                    // Xi set? Force match!
                    cnfConjuncts.add(this.formulaFactory.buildOr(overlapMatch, notXsI));
                    // None of these? No match!
                    if (notOverlapMatchPrevious != null) {
                        cnfConjuncts.add(this.formulaFactory.buildOr(notOverlapMatch, overlapMatchPrevious, xsI));
                    }
                    else {
                        cnfConjuncts.add(this.formulaFactory.buildOr(notOverlapMatch, xsI));
                    }
                    notOverlapMatchPrevious = notOverlapMatch;
                    overlapMatchPrevious = overlapMatch;
                }
                // For testing on a match: One of commonMatch (at the highest significance level)
                // or overlapMatch must have happened...
                cnfConjuncts.add(this.formulaFactory.buildOr(notIsGT, commonMatch, overlapMatch));
                // And one is enough.
                cnfConjuncts.add(this.formulaFactory.buildOr(isGT, notCommonMatch));
                cnfConjuncts.add(this.formulaFactory.buildOr(isGT, notOverlapMatch));
            }
            else {
                // For testing on a match: commonMatch must have happened...
                cnfConjuncts.add(this.formulaFactory.buildOr(notIsGT, commonMatch));
                // And that is enough.
                cnfConjuncts.add(this.formulaFactory.buildOr(isGT, notCommonMatch));

            }
            return this.formulaFactory.buildAnd(cnfConjuncts);
        }
        default:
            throw new RuntimeException("Unknown GTMode " + this.GT_MODE);
        }
    }

    /**
     * Builds a circuit which states that xs and ys
     * represent the same number.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return a circuit which represents that xs and ys
     *  represent the same number
     */
    @Override
    public Formula<None> buildEQCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        // make |xs| <= |ys| (= is symmetrical)
        if (xs.size() > ys.size()) {
            final List<? extends Formula<None>> tmpList = xs;
            xs = ys;
            ys = tmpList;
        }

        final int xsSize = xs.size();
        final int ysSize = ys.size();

        List<Formula<None>> pos0ToN;
        pos0ToN = new ArrayList<Formula<None>>(ysSize);

        for (int i = xsSize; i < ysSize; ++i) {
            pos0ToN.add(this.formulaFactory.buildNot(ys.get(i)));
        }
        for (int i = 0; i < xsSize; ++i) {
            pos0ToN.add(this.formulaFactory.buildIff(xs.get(i), ys.get(i)));
        }

        return this.formulaFactory.buildAnd(pos0ToN);
    }

    /**
     * Convenience method: Builds a circuit which states that xs represents
     * a number that is greater than or equal to the one ys represents.
     *
     * Based on buildGTCircuit and buildEQCircuit.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return x: the output of a circuit that represents "xs >= ys"
     *         y: the output of the subcircuit that represents "xs == ys"
     *            (useful for searchstrict mode)
     */
    @Override
    public Pair<Formula<None>, Formula<None>> buildGECircuit(final List<? extends Formula<None>> xs,
            final List<? extends Formula<None>> ys) {

        // just reduce to the definition: A >= B iff (A > B or A = B)
        final Formula<None> xsGTys = this.buildGTCircuit(xs, ys);
        final Formula<None> xsEQys = this.buildEQCircuit(xs, ys);
        final Formula<None> resultX = this.formulaFactory.buildOr(xsGTys, xsEQys);
        return new Pair<Formula<None>, Formula<None>>(resultX, xsEQys);
    }

    /**
     * Removes maximum proper ZERO^* suffixes from list.
     * Only the first element of list will never be removed
     * by cropList(list).
     *
     * Intention: Remove unnecessary ZEROs from the most
     * significant positions of list, based on the assumption
     * that list encodes a binary number.
     *
     * @param list list of formulae, encodes a natural number,
     *  possibly has unnecessary ZEROs at its most significant
     *  positions
     */
    private void cropList(final List<Formula<None>> list) {
        for (int i = list.size() - 1; i > 0; --i) {
            if (list.get(i) == this.ZERO) {
                // == is okay here, this.ZERO is the only allowed ZERO here
                list.remove(i);
            }
            else {
                return;
            }
        }

    }

    /**
     * Represent 2^xs.
     * @param xs The circuit of the exponent.
     * @return 2^xs.
     */
    @Override
    public PolyCircuit buildPowerOfTwo(final PolyCircuit xs) {
        if (Globals.useAssertions) {
            assert (xs != null);
        }
        final List<? extends Formula<None>> formulae = xs.getFormulae();
        if (Globals.useAssertions) {
            assert(formulae != null  && !formulae.isEmpty());
            // do not use crazy exponents
            assert (xs.getMax().compareTo(
                    BigInteger.valueOf(Integer.MAX_VALUE)) <= 0);
        }

        final int bits = xs.getMax().intValue() + 1;
        final int size = formulae.size();
        final List<Formula<None>> notFormulae = new ArrayList<Formula<None>>(size);
        for (int i = 0; i < size; ++i) {
            notFormulae.add(this.formulaFactory.buildNot(formulae.get(i)));
        }
        final List<Formula<None>> zs = new ArrayList<Formula<None>>(bits);

        for (int i = 0; i < bits; i++) {
            // i ranges over all possible exponents (positions in the bit array)
            // of the resulting expression
            final List<Formula<None>> positions = new ArrayList<Formula<None>>(size);
            for (int j = 0; j < size; j++) {
                // j ranges over all positions of the initial expression

                // define the value of 2^xs at position i (addend 2^i).
                // the first (0) bit of the result is only set when all bits
                // of xs are not set (meaning 2^0 = 1).
                // the fifth (4) bit of the result is set when exactly the
                // first (0) and third (2) bit are set (because 101 is the
                // bit representation of 5).

                if ((i & (1 << j)) != 0) {
                    positions.add(formulae.get(j));
                } else {
                    positions.add(notFormulae.get(j));
                }
            }
            final Formula<None> formula = this.formulaFactory.buildAnd(positions);
            zs.add(formula);
        }

        if (this.TRACKING) {
            return new PolyCircuit(zs,
                    BigInteger.ONE.shiftLeft(xs.getMax().intValue()));
        } else {
            return new PolyCircuit(zs, BigInteger.ZERO);
        }
    }

    @Override
    public PolyCircuit buildShiftRightBinary(final PolyCircuit shiftBy, final PolyCircuit xs) {
        final long time = System.nanoTime();

        final List<Formula<None>> zs = this.buildShiftRightBinary(shiftBy.getFormulae(), xs.getFormulae());
        if (this.TRACKING) {
            final BigInteger zsMax = xs.getMax().multiply(shiftBy.getMax());
            if (zsMax.signum() == 0) {
                final Formula<None> ff = this.formulaFactory.buildConstant(false);
                return new PolyCircuit(Collections.singletonList(ff), zsMax);
            }
            //log.log(Level.FINER, "Inputs: " + xs.getFormulae().toString() + " << " + shiftBy.getFormulae().toString());
            //log.log(Level.FINER, "Built shift (" + zsMax + "): " + zs.toString());
            //log.log(Level.FINEST, "Building one binary shift took " + (System.nanoTime() - time) + "ns\n");
            return new PolyCircuit(zs, zsMax);

        }
        else {
            return new PolyCircuit(zs, BigInteger.ZERO);
        }
    }

    private List<Formula<None>> buildShiftRightBinary(final List<Formula<None>> shiftBy,
        final List<Formula<None>> xs) {
        // We implement binary shift by means of a barrel shifter.
        // This works as such: For each bit in shiftBy, we build a circuit
        // oring the result of that circuit padded with zeroes and the circuit shifted by
        // the appropriate number of bits.
        // In order to save junctors, we build this bottom-up from the least order bit.

        List<Formula<None>> currentInput = xs;

        for (int i = 0; i < shiftBy.size(); i++) {
            final int sB = AProVEMath.power(2, i);
            final List<Formula<None>> shifted = new ArrayList<Formula<None>> (currentInput.size() + sB);
            for (int j = 0; j < sB; j++) {
                shifted.add(this.formulaFactory.buildConstant(false));
            }
            shifted.addAll(currentInput);
            //log.log(Level.FINEST, ">>:" + shifted.toString());
            //log.log(Level.FINEST, "<<:" + currentInput.toString());
            currentInput = this.buildBitwiseOrCircuit(this.bitAnd(this.formulaFactory.buildNot(shiftBy.get(i)), currentInput), this.bitAnd(shiftBy.get(i), shifted));
            //log.log(Level.FINEST, shifted.toString());
        }


        return currentInput;
    }

    /**
     * Ands a factor to all circuits in a list and returns the resulting circuit.
     * @param andFactor
     * @param xs
     * @return
     */
    private List<Formula<None>> bitAnd(final Formula<None> andFactor,
        final List<Formula<None>> xs) {
        final List<Formula<None>> ret = new ArrayList<Formula<None>> (xs.size());
        for (int i=0; i < xs.size(); i++) {
            ret.add(this.formulaFactory.buildAnd(andFactor, xs.get(i)));
        }
        return ret;
    }
}
