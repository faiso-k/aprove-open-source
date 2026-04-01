package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Constructs some predefined formulae which denote that
 * some Atom tuples are in certain relations. Note that
 * any List you pass to the methods will be incorporated
 * into the built formulae, so changing the lists or their
 * elements afterwards will change the formulae, too.
 *
 * Note: This factory is designed to be used with the
 * (now obsolete) SPCToFormulaConverter. You probably
 * do not want to use it.
 * It was previously known as PredefinedFormulaFactory
 * (-> CVS history).
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class ArithmeticFormulaFactory {

    private FormulaFactory<None> formulaFactory;
    // used for building new "local" variables

    private final Constant<None> ZERO;
    // to be used in the formulae, e.g. for padding of shifted values

    private ArithmeticFormulaFactory(FormulaFactory<None> formulaFactory) {
        this.formulaFactory = formulaFactory;
        this.ZERO = this.formulaFactory.buildConstant(false);
    }

    /**
     * Creates a new ArithmeticFormulaFactory which uses varFactory to get new
     * variables.
     *
     * @param varFactory the FormulaFactory to be used
     * @return a new ArithmeticFormulaFactory
     */
    public static ArithmeticFormulaFactory create(FormulaFactory<None> varFactory) {
        return new ArithmeticFormulaFactory(varFactory);
    }


    /*
     * Small guide to understanding this class:
     * - The methods are based on certain formulae. TODO
     *   You are assumed to have access to the corresponding document,
     *   otherwise understanding might require some reverse engineering of
     *   the formulae from the code (not too difficult, but nasty).
     * - The set of positions is assumed to be (set of natural numbers)^*,
     *   hence the first argument of a junctor at the root position is at
     *   position 0 (not 1!). This is for the sake of avoiding needless
     *   off by one errors.
     * - Let <p> \in Nats^*. Java variables named pos<p> are used to contain
     *   the formula at position <p>. Variables named pos<p>0To<p>n
     *   are used to contain the arguments of the NaryJunctorFormula
     *   at position <p>.
     * - By convention, "input" variable lists are called xs and ys,
     *   "output" variable lists are called zs. None of the lists may
     *   be empty. The output lists must contain a "suitable" (depends on
     *   the method) number of variables.
     */

    /**
     * Builds a formula which expresses that xs, ys and zs are the
     * binary representations of numbers such that "xs * ys == zs".
     * The formula works similar to the elementary school algorithm
     * which reduces multiplication to a series of additions (especially
     * suitable for binary numbers).
     *
     * @param xs first multiplicand, non-empty
     * @param ys second multiplicand, non-empty
     * @param zs result of the multiplication, muste be of size
     *  xs.size()+ys.size() when the method is called
     * @return a formula which represents that xs * ys == zs
     */
    public Formula<None> buildTimesFormula(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys, List<? extends Formula<None>> zs) {
        return this.formulaFactory.buildAnd(this.buildTimesConjuncts(xs, ys, zs));
    }

    /**
     * @param xs first multiplicand
     * @param ys second multiplicand
     * @param zs supposed to take the values of xs * ys, must be of size
     *  xs.size() + ys.size() when the method is called
     * @return the conjuncts of an AndFormula which would express that
     *  xs * ys == zs
     */
    List<? extends Formula<None>> buildTimesConjuncts(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys, List<? extends Formula<None>> zs) {
        if (Globals.useAssertions) {
            assert (! xs.isEmpty());
            assert (! ys.isEmpty());
            assert (zs.size() == xs.size() + ys.size());
        }

        // it is convenient to have the first multiplicand be
        // at least as long as the second one, swap if necessary
        // (use commutativity of times)
        if (xs.size() < ys.size()) {
            List<? extends Formula<None>> tmpList = xs;
            xs = ys;
            ys = tmpList;
        }

        int xsSize = xs.size();
        int ysSize = ys.size();
        int zsSize = zs.size();

        switch (ysSize) {
        case 1: // implementation slightly deviates from the document
                // (\lnot Z_{k+1} is not an extra conjunct here),
                // otherwise messing with sublists would have been the
                // way to go, with all the bugs this could introduce
        {
            List<Formula<None>> pos0To1 = new ArrayList<Formula<None>>(2);
            List<Formula<None>> pos00To01, pos10To11;

            pos00To01 = new ArrayList<Formula<None>>(2);
            pos00To01.add(this.formulaFactory.buildNot(ys.get(0)));
            pos00To01.add(this.buildEQFormula(xs, zs));
            pos0To1.add(this.formulaFactory.buildOr(pos00To01));

            pos10To11 = new ArrayList<Formula<None>>(2);
            pos10To11.add(ys.get(0));

            List<Formula<None>> pos110To11N;
            pos110To11N = new ArrayList<Formula<None>>(zsSize);
            for (int i = 0; i < zsSize; ++i) {
                pos110To11N.add(this.formulaFactory.buildNot(zs.get(i)));
            }
            pos10To11.add(this.formulaFactory.buildAnd(pos110To11N));
            pos0To1.add(this.formulaFactory.buildOr(pos10To11));
            return pos0To1;
        }
        case 2:
        {
            List<Formula<None>> pos0To3 = new ArrayList<Formula<None>>(4);
            List<Formula<None>> pos00To02, pos10To12, pos20To22, pos30To32;

            // will be needed twice, share it
            List<Formula<None>> zeroThenXs = new ArrayList<Formula<None>>(xsSize+1);
            zeroThenXs.add(this.ZERO);
            zeroThenXs.addAll(xs);

            // new blocks are used for earlier detection of errors
            // caused by typos in the identifiers
            {
                pos00To02 = new ArrayList<Formula<None>>(3);
                pos00To02.add(this.formulaFactory.buildNot(ys.get(0)));
                pos00To02.add(this.formulaFactory.buildNot(ys.get(1)));

                pos00To02.add(this.buildPlusFormula(xs, zeroThenXs, zs));
                pos0To3.add(this.formulaFactory.buildOr(pos00To02));
            }

            {
                pos10To12 = new ArrayList<Formula<None>>(3);
                pos10To12.add(this.formulaFactory.buildNot(ys.get(0)));
                pos10To12.add(ys.get(1));

                pos10To12.add(this.buildEQFormula(xs, zs));
                pos0To3.add(this.formulaFactory.buildOr(pos10To12));
            }

            {
                pos20To22 = new ArrayList<Formula<None>>(3);
                pos20To22.add(ys.get(0));
                pos20To22.add(this.formulaFactory.buildNot(ys.get(1)));

                pos20To22.add(this.buildEQFormula(zeroThenXs, zs));
                pos0To3.add(this.formulaFactory.buildOr(pos20To22));
            }

            {
                pos30To32 = new ArrayList<Formula<None>>(3);
                pos30To32.add(ys.get(0));
                pos30To32.add(ys.get(1));

                List<Formula<None>> pos320To32N = new ArrayList<Formula<None>>(zsSize);
                for (int i = 0; i < zsSize; ++i) {
                    pos320To32N.add(this.formulaFactory.buildNot(zs.get(i)));
                }
                pos30To32.add(this.formulaFactory.buildAnd(pos320To32N));
                pos0To3.add(this.formulaFactory.buildOr(pos30To32));
            }
            return pos0To3;
        }
        default:
            List<List<Variable<None>>> addends; // will contain the intermediate sums
            // (List<Variable>[] would have been better, but arrays and
            // generics do not play along too well)

            int addendsSize = ysSize - 2;
            addends = new ArrayList<List<Variable<None>>>(addendsSize);
            int xsSizePlus2 = xsSize + 2;
            for (int i = 0; i < addendsSize; ++i) {
                int currentAddendSize = xsSizePlus2 + i;
                List<Variable<None>> currentAddend = new ArrayList<Variable<None>>(currentAddendSize);
                for (int j = 0; j < currentAddendSize; ++j) {
                    currentAddend.add(this.formulaFactory.buildVariable());
                }
                addends.add(currentAddend);
            }

            List<Formula<None>> pos0ToN = new ArrayList<Formula<None>>(2*ysSize);

            List<Variable<None>> addendsElement0 = addends.get(0);
            // will be needed several times, do not repeat get(0) unnecessarily

            // the first four conjuncts:
            // we fill the first addend, (really) similar to case 2
            List<Formula<None>> pos00To02, pos10To12, pos20To22, pos30To32;

            // will be needed twice, share it
            List<Formula<None>> zeroThenXs = new ArrayList<Formula<None>>(xsSize+1);
            zeroThenXs.add(this.ZERO);
            zeroThenXs.addAll(xs);

            // new blocks are used for earlier detection of errors
            // caused by typos in the identifiers
            {
                pos00To02 = new ArrayList<Formula<None>>(3);
                pos00To02.add(this.formulaFactory.buildNot(ys.get(0)));
                pos00To02.add(this.formulaFactory.buildNot(ys.get(1)));

                pos00To02.add(this.buildPlusFormula(xs, zeroThenXs, addendsElement0));
                pos0ToN.add(this.formulaFactory.buildOr(pos00To02));
            }

            {
                pos10To12 = new ArrayList<Formula<None>>(3);
                pos10To12.add(this.formulaFactory.buildNot(ys.get(0)));
                pos10To12.add(ys.get(1));

                pos10To12.add(this.buildEQFormula(xs, addendsElement0));
                pos0ToN.add(this.formulaFactory.buildOr(pos10To12));
            }

            {
                pos20To22 = new ArrayList<Formula<None>>(3);
                pos20To22.add(ys.get(0));
                pos20To22.add(this.formulaFactory.buildNot(ys.get(1)));

                pos20To22.add(this.buildEQFormula(zeroThenXs, addendsElement0));
                pos0ToN.add(this.formulaFactory.buildOr(pos20To22));
            }

            {
                pos30To32 = new ArrayList<Formula<None>>(3);
                pos30To32.add(ys.get(0));
                pos30To32.add(ys.get(1));

                int addend0Size = addendsElement0.size();
                List<Formula<None>> pos320To32N = new ArrayList<Formula<None>>(addend0Size);
                for (int i = 0; i < addend0Size; ++i) {
                    pos320To32N.add(this.formulaFactory.buildNot(addendsElement0.get(i)));
                }
                pos30To32.add(this.formulaFactory.buildAnd(pos320To32N));
                pos0ToN.add(this.formulaFactory.buildOr(pos30To32));
            }

            // now to the other addends:

            // the next 2*ysSize-6 conjuncts
            {
                int iterEnd = ysSize - 3;
                for (int i = 1; i <= iterEnd; ++i) {
                    List<Formula<None>> posI0ToI1 = new ArrayList<Formula<None>>(2);
                    List<Formula<None>> posJ0ToJ1 = new ArrayList<Formula<None>>(2);

                    List<Formula<None>> iPlusOneZerosXs = new ArrayList<Formula<None>>(xsSize+i+1);
                    for (int k = 0; k <= i; ++k) {
                        iPlusOneZerosXs.add(this.ZERO);
                    }
                    iPlusOneZerosXs.addAll(xs);

                    posI0ToI1.add(this.formulaFactory.buildNot(ys.get(i+1)));
                    posI0ToI1.add(this.buildPlusFormula(addends.get(i-1), iPlusOneZerosXs, addends.get(i)));

                    pos0ToN.add(this.formulaFactory.buildOr(posI0ToI1));

                    posJ0ToJ1.add(ys.get(i+1));
                    posJ0ToJ1.add(this.buildEQFormula(addends.get(i-1), addends.get(i)));

                    pos0ToN.add(this.formulaFactory.buildOr(posJ0ToJ1));
                }

            }

            // the last two conjuncts
            {
                int ysSizeMinusOne = ysSize - 1;
                List<Formula<None>> ysSizeMinusOneZerosXs = new ArrayList<Formula<None>>(ysSizeMinusOne + xsSize);
                for (int i = 0; i < ysSizeMinusOne; ++i) {
                    ysSizeMinusOneZerosXs.add(this.ZERO);
                }
                ysSizeMinusOneZerosXs.addAll(xs);

                List<Formula<None>> posI0ToI1 = new ArrayList<Formula<None>>(2);
                List<Formula<None>> posJ0ToJ1 = new ArrayList<Formula<None>>(2);

                posI0ToI1.add(this.formulaFactory.buildNot(ys.get(ysSize-1)));
                posI0ToI1.add(this.buildPlusFormula(addends.get(ysSize-3), ysSizeMinusOneZerosXs, zs));

                pos0ToN.add(this.formulaFactory.buildOr(posI0ToI1));

                posJ0ToJ1.add(ys.get(ysSize-1));
                posJ0ToJ1.add(this.buildEQFormula(addends.get(ysSize-3), zs));

                pos0ToN.add(this.formulaFactory.buildOr(posJ0ToJ1));

                if (Globals.useAssertions) {
                    assert (pos0ToN.size() == 2 * ysSize);
                }
            }
            return pos0ToN;
        }
    }

    /**
     * Builds a formula which encodes that xs + ys = zs where
     * xs, ys and zs represent binary encoding of natural numbers.
     * The formula is based on the elementary school algorithm
     * which uses carry bits.
     *
     * @param xs the first addend, not empty
     * @param ys the second addend, not empty
     * @param zs the result, must be of size max(xs.size(),ys.size()) + 1
     *   when the method is called
     * @return the constructed formula
     */
    public Formula<None> buildPlusFormula(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys, List<? extends Formula<None>> zs) {
        return this.formulaFactory.buildAnd(this.buildPlusConjuncts(xs, ys, zs));
    }

    List<? extends Formula<None>> buildPlusConjuncts(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys, List<? extends Formula<None>> zs) {
        if (Globals.useAssertions) {
            assert (! xs.isEmpty());
            assert (! ys.isEmpty());
            assert (zs.size() == (Math.max(xs.size(),ys.size())+1));
        }

        int xsSize = xs.size(); // size from input
        int ysSize = ys.size(); // size from input
        boolean xsGTys = (xsSize > ysSize);
        int zsSize = zs.size(); // size after filling

        // special cases:
        // 1) both addends have just 1 bit, no carry bits needed
        if (xsSize == 1 && ysSize == 1) {
            // the variable names will be understandable if you have a look at
            // the corresponding PL formulae, result would be posEpsilon then
            List<Formula<None>> pos0To1;

            Formula<None> pos00, pos01;
            Formula<None> pos10, pos11;
            List<Formula<None>> pos000To001, pos100To101;

            pos000To001 = new ArrayList<Formula<None>>(2);
            pos000To001.add(xs.get(0));
            pos000To001.add(ys.get(0));

            pos100To101 = new ArrayList<Formula<None>>(2);
            pos100To101.add(xs.get(0));
            pos100To101.add(ys.get(0));

            pos00 = this.formulaFactory.buildXor(pos000To001);
            pos01 = zs.get(0);

            pos10 = this.formulaFactory.buildAnd(pos100To101);
            pos11 = zs.get(1);

            pos0To1 = new ArrayList<Formula<None>>(2);
            pos0To1.add(this.formulaFactory.buildIff(pos00, pos01));
            pos0To1.add(this.formulaFactory.buildIff(pos10, pos11));

            return pos0To1;
        }
        // 2) xs and ys are of the same size, but bigger than one
        else if (xsSize == ysSize) {
            // carries will contain the (implicitly existentially quantified)
            // variables which contain the carry of the addition. we do not
            // care about the interpretation of the carry bits afterwards.
            Variable<None>[] carries = new Variable[xsSize-1];
            for (int i = 0; i < carries.length; ++i) {
                carries[i] = this.formulaFactory.buildVariable();
            }

            List<Formula<None>> pos0ToN; // N = 2*xsSize - 1
            pos0ToN = new ArrayList<Formula<None>>(2*xsSize);

            // use additional blocks to make (some) typos compile-time errors.
            {
                // first conjunct
                Formula<None> pos0, pos00, pos01;
                List<Formula<None>> pos000To001;

                pos000To001 = new ArrayList<Formula<None>>(2);
                pos000To001.add(xs.get(0));
                pos000To001.add(ys.get(0));

                pos00 = this.formulaFactory.buildXor(pos000To001);
                pos01 = zs.get(0);
                pos0 = this.formulaFactory.buildIff(pos00, pos01);
                pos0ToN.add(pos0);
            }

            {
                // second conjunct
                Formula<None> pos1, pos10, pos11;
                List<Formula<None>> pos100To101;

                pos100To101 = new ArrayList<Formula<None>>(2);
                pos100To101.add(xs.get(0));
                pos100To101.add(ys.get(0));

                pos10 = this.formulaFactory.buildAnd(pos100To101);
                pos11 = carries[0];
                pos1 = this.formulaFactory.buildIff(pos10, pos11);
                pos0ToN.add(pos1);
            }

            {
                // third, ..., xsSize+1st conjunct
                int iterEnd = xsSize - 1;
                for (int i = 1; i <= iterEnd; ++i) {
                    Formula<None> posI0, posI1;
                    List<Formula<None>> posI00ToI02;

                    posI00ToI02 = new ArrayList<Formula<None>>(3);
                    posI00ToI02.add(xs.get(i));
                    posI00ToI02.add(ys.get(i));
                    posI00ToI02.add(carries[i-1]);

                    posI0 = this.formulaFactory.buildXor(posI00ToI02);
                    posI1 = zs.get(i);
                    pos0ToN.add(this.formulaFactory.buildIff(posI0, posI1));
                }
            }

            {
                // xsSize+2nd, ..., 2*xsSize-1st conjunct
                int iterEnd = xsSize - 2;
                for (int i = 1; i <= iterEnd; ++i) {
                    Formula<None> posI0, posI1;
                    List<Formula<None>> posI00ToI02;
                    List<Formula<None>> posI000ToI001, posI010ToI011, posI020ToI021;

                    posI000ToI001 = new ArrayList<Formula<None>>(2);
                    posI000ToI001.add(xs.get(i));
                    posI000ToI001.add(ys.get(i));

                    posI010ToI011 = new ArrayList<Formula<None>>(2);
                    posI010ToI011.add(carries[i-1]);
                    posI010ToI011.add(xs.get(i));

                    posI020ToI021 = new ArrayList<Formula<None>>(2);
                    posI020ToI021.add(carries[i-1]);
                    posI020ToI021.add(ys.get(i));

                    posI00ToI02 = new ArrayList<Formula<None>>(3);
                    posI00ToI02.add(this.formulaFactory.buildOr(posI000ToI001));
                    posI00ToI02.add(this.formulaFactory.buildOr(posI010ToI011));
                    posI00ToI02.add(this.formulaFactory.buildOr(posI020ToI021));

                    posI0 = this.formulaFactory.buildAnd(posI00ToI02);
                    posI1 = carries[i];
                    pos0ToN.add(this.formulaFactory.buildIff(posI0, posI1));
                }
            }

            {
                // 2*xsSizeth conjunct
                Formula<None> posN0, posN1; // N = 2*xsSize - 1
                List<Formula<None>> posN00ToN02;
                List<Formula<None>> posN000ToN001, posN010ToN011, posN020ToN021;

                posN000ToN001 = new ArrayList<Formula<None>>(2);
                posN000ToN001.add(xs.get(xsSize-1));
                posN000ToN001.add(ys.get(xsSize-1));

                posN010ToN011 = new ArrayList<Formula<None>>(2);
                posN010ToN011.add(carries[xsSize-2]);
                posN010ToN011.add(xs.get(xsSize-1));

                posN020ToN021 = new ArrayList<Formula<None>>(2);
                posN020ToN021.add(carries[xsSize-2]);
                posN020ToN021.add(ys.get(xsSize-1));

                posN00ToN02 = new ArrayList<Formula<None>>(3);
                posN00ToN02.add(this.formulaFactory.buildOr(posN000ToN001));
                posN00ToN02.add(this.formulaFactory.buildOr(posN010ToN011));
                posN00ToN02.add(this.formulaFactory.buildOr(posN020ToN021));

                posN0 = this.formulaFactory.buildAnd(posN00ToN02);
                posN1 = zs.get(zsSize-1);
                pos0ToN.add(this.formulaFactory.buildIff(posN0, posN1));
            }

            if (Globals.useAssertions) {
                assert (pos0ToN.size() == 2*xsSize);
            }

            return pos0ToN;
        }
        // 3) xsSize != ysSize
        else {
            if (xsGTys) {
                // swap xs and ys so we only have to regard the case
                // xs.size() < ys.size(), plus is commutative :)
                List<? extends Formula<None>> tmpList;
                tmpList = xs;
                xs = ys;
                ys = tmpList;

                int tmpSize;
                tmpSize = xsSize;
                xsSize = ysSize;
                ysSize = tmpSize;
            }

            // carries will contain the (implicitly existentially quantified)
            // variables which contain the carry of the addition. we do not
            // care about the interpretation of the carry bits afterwards.
            Variable<None>[] carries = new Variable[ysSize-1];
            for (int i = 0; i < carries.length; ++i) {
                carries[i] = this.formulaFactory.buildVariable();
            }

            List<Formula<None>> pos0ToN; // N = 2*ysSize - 1
            pos0ToN = new ArrayList<Formula<None>>(2*ysSize);

            // use additional blocks to make (some) typos compile-time errors.
            {
                // first conjunct
                Formula<None> pos0, pos00, pos01;
                List<Formula<None>> pos000To001;

                pos000To001 = new ArrayList<Formula<None>>(2);
                pos000To001.add(xs.get(0));
                pos000To001.add(ys.get(0));

                pos00 = this.formulaFactory.buildXor(pos000To001);
                pos01 = zs.get(0);
                pos0 = this.formulaFactory.buildIff(pos00, pos01);
                pos0ToN.add(pos0);
            }

            {
                // second conjunct
                Formula<None> pos1, pos10, pos11;
                List<Formula<None>> pos100To101;

                pos100To101 = new ArrayList<Formula<None>>(2);
                pos100To101.add(xs.get(0));
                pos100To101.add(ys.get(0));

                pos10 = this.formulaFactory.buildAnd(pos100To101);
                pos11 = carries[0];
                pos1 = this.formulaFactory.buildIff(pos10, pos11);
                pos0ToN.add(pos1);
            }

            {
                // third, ..., xsSize+1st conjunct
                int iterEnd = xsSize - 1;
                for (int i = 1; i <= iterEnd; ++i) {
                    Formula<None> posI0, posI1;
                    List<Formula<None>> posI00ToI02;

                    posI00ToI02 = new ArrayList<Formula<None>>(3);
                    posI00ToI02.add(xs.get(i));
                    posI00ToI02.add(ys.get(i));
                    posI00ToI02.add(carries[i-1]);

                    posI0 = this.formulaFactory.buildXor(posI00ToI02);
                    posI1 = zs.get(i);
                    pos0ToN.add(this.formulaFactory.buildIff(posI0, posI1));
                }
            }

            {
                // xsSize+2nd, ..., ysSize+1st conjunct
                int iterEnd = ysSize - 1;
                for (int i = xsSize; i <= iterEnd; ++i) {
                    Formula<None> posI0, posI1;
                    List<Formula<None>> posI00ToI01;

                    posI00ToI01 = new ArrayList<Formula<None>>(2);
                    posI00ToI01.add(ys.get(i));
                    posI00ToI01.add(carries[i-1]);

                    posI0 = this.formulaFactory.buildXor(posI00ToI01);
                    posI1 = zs.get(i);
                    pos0ToN.add(this.formulaFactory.buildIff(posI0, posI1));
                }
            }

            {
                // ysSize+2nd, ..., xsSize+ysSizeth conjunct
                int iterEnd = xsSize - 1;
                for (int i = 1; i <= iterEnd; ++i) {
                    Formula<None> posI0, posI1;
                    List<Formula<None>> posI00ToI02;
                    List<Formula<None>> posI000ToI001, posI010ToI011, posI020ToI021;

                    posI000ToI001 = new ArrayList<Formula<None>>(2);
                    posI000ToI001.add(xs.get(i));
                    posI000ToI001.add(ys.get(i));

                    posI010ToI011 = new ArrayList<Formula<None>>(2);
                    posI010ToI011.add(carries[i-1]);
                    posI010ToI011.add(xs.get(i));

                    posI020ToI021 = new ArrayList<Formula<None>>(2);
                    posI020ToI021.add(carries[i-1]);
                    posI020ToI021.add(ys.get(i));

                    posI00ToI02 = new ArrayList<Formula<None>>(3);
                    posI00ToI02.add(this.formulaFactory.buildOr(posI000ToI001));
                    posI00ToI02.add(this.formulaFactory.buildOr(posI010ToI011));
                    posI00ToI02.add(this.formulaFactory.buildOr(posI020ToI021));

                    posI0 = this.formulaFactory.buildAnd(posI00ToI02);
                    posI1 = carries[i];
                    pos0ToN.add(this.formulaFactory.buildIff(posI0, posI1));
                }
            }

            {
                // xsSize+ysSize+1st, ..., 2*ysSize-1st conjunct
                int iterEnd = ysSize - 2;
                for (int i = xsSize; i <= iterEnd; ++i) {
                    Formula<None> posI0, posI1;
                    List<Formula<None>> posI00ToI01;

                    posI00ToI01 = new ArrayList<Formula<None>>(2);
                    posI00ToI01.add(carries[i-1]);
                    posI00ToI01.add(ys.get(i));

                    posI0 = this.formulaFactory.buildAnd(posI00ToI01);
                    posI1 = carries[i];
                    pos0ToN.add(this.formulaFactory.buildIff(posI0, posI1));
                }
            }

            {
                // 2*ysSizeth conjunct
                Formula<None> posN0, posN1; // N = 2*ysSize - 1
                List<Formula<None>> posN00ToN01;

                posN00ToN01 = new ArrayList<Formula<None>>(2);
                posN00ToN01.add(ys.get(ysSize-1));
                posN00ToN01.add(carries[ysSize-2]);

                posN0 = this.formulaFactory.buildAnd(posN00ToN01);
                posN1 = zs.get(zsSize-1);
                pos0ToN.add(this.formulaFactory.buildIff(posN0, posN1));
            }

            if (Globals.useAssertions) {
                assert (pos0ToN.size() == 2*ysSize);
            }

            return pos0ToN;
        }
    }

    /**
     * Builds a formula which represents that xs > ys.
     *
     * @param xs non-empty list of Atoms
     * @param ys non-empty list of Atoms
     * @return a formula which represents that xs > ys
     */
    public Formula<None> buildGTFormula(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        if (Globals.useAssertions) {
            assert (! xs.isEmpty());
            assert (! ys.isEmpty());
        }

        List<? extends Formula<None>> gtConjuncts;
        gtConjuncts = this.buildGTConjuncts(xs, ys);
        if (gtConjuncts.size() < 2) {
            // conjunction over 1 formula is the formula itself,
            // case of 0 formulae should not happen here
            return gtConjuncts.get(0);
        }
        else {
            return this.formulaFactory.buildAnd(gtConjuncts);
        }
    }


    public List<? extends Formula<None>> buildGTConjuncts(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        int xsSize = xs.size();
        int ysSize = ys.size();

        // The construction of the > formula is not quite symmetric.
        // We need to distinguish between |xs| < |ys| and |xs| >= |ys|.
        boolean xsSizeLTysSize = xsSize < ysSize;
        int minSize = xsSizeLTysSize ? xsSize : ysSize;

        // Common feature: We will have a subformula which encodes that for
        // k = min(xsSize, ysSize), the numbers that correspond to the prefixes
        // of length k of xs and ys are in relation >. Note that it will not be
        // used at the same positions, though.
        //
        // Here, all ppos* var names consider the root position
        // /of the aformentioned subformula/ to be epsilon. This is contrary
        // to the usual custom of treating the root position of
        // the /resulting formula of the whole method/ as epsilon.
        // So distinguish ppos* and pos*.

        List<Formula<None>> ppos0ToN;
        // N = xsSize-1, see the formulae in the document on why this is
        // okay regardless of xsSizeLEysSize; if xsSize > ysSize, we will
        // need the additional space

        List<Formula<None>> pposI0ToIP = null;
        {
            ppos0ToN = new ArrayList<Formula<None>>(xsSize);
            for (int i = 0; i < minSize; ++i) {
                // P = 2+minSize-i TODO -1, I think
                pposI0ToIP = new ArrayList<Formula<None>>(2+minSize-i);
                pposI0ToIP.add(xs.get(i));
                pposI0ToIP.add(this.formulaFactory.buildNot(ys.get(i)));
                for (int j = i + 1; j < minSize; ++j) {
                    pposI0ToIP.add(this.formulaFactory.buildIff(xs.get(j), ys.get(j)));
                }
                ppos0ToN.add(this.formulaFactory.buildAnd(pposI0ToIP));
            }
            // ppos0ToN is a (possibly singleton) set of disjuncts.
            // If it is a singleton, we can omit the wrapping OrFormula
            // altogether, we just need to regard the element of the singleton.
            // This in turn is an AndFormula. So do not just blindly create an
            // OrFormula with ppos0ToN as arguments, but check its size first.
        }

        // Now two cases for constructing the rest:
        if (xsSizeLTysSize) {
            // We will get several conjuncts as result.

            List<Formula<None>> pos0ToN;
            if (ppos0ToN.size() == 1) {
                pos0ToN = new ArrayList<Formula<None>>(ysSize - xsSize + pposI0ToIP.size());
            }
            else {
                pos0ToN = new ArrayList<Formula<None>>(ysSize-xsSize+1);
            }

            // all more significant bits than the first minSize ones have
            // to be 0
            for (int i = xsSize; i < ysSize; ++i) {
                pos0ToN.add(this.formulaFactory.buildNot(ys.get(i)));
            }

            // now to the less significant bits
            if (Globals.useAssertions) {
                assert (ppos0ToN.size() > 0);
            }

            if (ppos0ToN.size() == 1) {
                // pposI0ToIP contains the conjuncts which we want.
                // This approach is a bit ugly, but we want to avoid nary
                // FooFormulae which again have a FooFormula as argument
                // at all costs (only BarFormulae are okay).
                pos0ToN.addAll(pposI0ToIP);
            }
            else {
                pos0ToN.add(this.formulaFactory.buildOr(ppos0ToN));
            }
            return pos0ToN;
        }
        else {
            // We will get an OrFormula as result. Since we already need a
            // disjunction for the first minSize bits, we can as well extend
            // the list ppos0ToN which contains the arguments of this
            // disjunction.

            // Note that the order of the conjunct is different in the
            // document. TODO check document

            for (int i = ysSize; i < xsSize; ++i) {
                ppos0ToN.add(xs.get(i));
            }

            if (ppos0ToN.size() > 1) {
                List<Formula<None>> pos0To0 = new ArrayList<Formula<None>>(1);
                pos0To0.add(this.formulaFactory.buildOr(ppos0ToN));
                return pos0To0;
            }
            else {
                // disjunction of 1 element -> just the element itself
                return ppos0ToN;
            }
        }
    }

    /**
     * Builds a formula which states that xs and ys
     * represent the same number.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return a formula which represents that xs and ys
     *  represent the same number
     */
    public Formula<None> buildEQFormula(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        return this.formulaFactory.buildAnd(this.buildEQConjuncts(xs, ys));
    }

    List<? extends Formula<None>> buildEQConjuncts(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        // make |xs| <= |ys| (= is symmetrical)
        if (xs.size() > ys.size()) {
            List<? extends Formula<None>> tmpList = xs;
            xs = ys;
            ys = tmpList;
        }

        int xsSize = xs.size();
        int ysSize = ys.size();

        List<Formula<None>> pos0ToN;
        pos0ToN = new ArrayList<Formula<None>>(ysSize);

        for (int i = xsSize; i < ysSize; ++i) {
            pos0ToN.add(this.formulaFactory.buildNot(ys.get(i)));
        }

        for (int i = 0; i < xsSize; ++i) {
            pos0ToN.add(this.formulaFactory.buildIff(xs.get(i), ys.get(i)));
        }
        return pos0ToN;
    }

}
