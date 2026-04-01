package aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.Nat;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SatSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * A CircuitFactory for constraints over natural numbers.
 * This is mostly C&P (somewhat cleaned up) from the older
 * ArithmeticCircuitFactory.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class NatCircuitFactory extends CircuitFactory {

    public NatCircuitFactory(FormulaFactory<None> formulaFactory) {
        super(formulaFactory);
    }

    @Override
    public Formula<None> buildGTCircuit(
            List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        int xsSize = xs.size();
        int ysSize = ys.size();

        Formula<None> result;
        if (xsSize == 1 && ysSize == 1) {
            result = this.formulaFactory.buildAnd(xs.get(0),
                    this.formulaFactory.buildNot(ys.get(0)));
        }
        else if (xsSize > ysSize) {
            List<Formula<None>> args = new ArrayList<Formula<None>>(1+xsSize-ysSize);
            for (int i = ysSize; i < xsSize; ++i) {
                args.add(xs.get(i));
            }
            List<Formula<None>> newXs = new ArrayList<Formula<None>>(ysSize);
            for (int i = 0; i < ysSize; ++i) {
                newXs.add(xs.get(i));
            }
            args.add(this.buildGTCircuit(/*xs.subList(0, ysSize)*/newXs, ys));
            result = this.formulaFactory.buildOr(args);
        }
        else if (xsSize < ysSize) {
            List<Formula<None>> args = new ArrayList<Formula<None>>(1+ysSize-xsSize);
            for (int i = xsSize; i < ysSize; ++i) {
                args.add(this.formulaFactory.buildNot(ys.get(i)));
            }
            List<Formula<None>> newYs = new ArrayList<Formula<None>>(xsSize);
            for (int i = 0; i < xsSize; ++i) {
                newYs.add(ys.get(i));
            }
            args.add(this.buildGTCircuit(xs, /*ys.subList(0, xsSize)*/newYs));
            result = this.formulaFactory.buildAnd(args);
        }
        else { // xsSize == ysSize, xsSize != 1
            Formula<None> lastX = xs.get(xsSize - 1);
            Formula<None> lastY = ys.get(ysSize - 1);
            Formula<None> leftDisjunct = this.formulaFactory.buildAnd(lastX,
                    this.formulaFactory.buildNot(lastY));

            Formula<None> eqConjunct = this.formulaFactory.buildIff(lastX, lastY);

            List<Formula<None>> newXs, newYs;
            newXs = new ArrayList<Formula<None>>(xsSize-1);
            newYs = new ArrayList<Formula<None>>(xsSize-1);
            for (int i = 0; i < xsSize - 1; ++i) {
                newXs.add(xs.get(i));
                newYs.add(ys.get(i));
            }
            Formula<None> recursivelyBuiltConjunct = this.buildGTCircuit(/*xs.subList(0, xsSize-1)*/newXs, /*ys.subList(0, ysSize-1)*/newYs);
            Formula<None> rightDisjunct = this.formulaFactory.buildAnd(eqConjunct, recursivelyBuiltConjunct);
            result = this.formulaFactory.buildOr(leftDisjunct, rightDisjunct);
        }
        return result;
    }

    @Override
    public Formula<None> buildEQCircuit(
            List<? extends Formula<None>> xs,
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

        return this.formulaFactory.buildAnd(pos0ToN);
    }

    /**
     * @param xs - the first factor
     * @param ys - the second factor
     * @return
     *  x - circuit for the product of xs and ys<br>
     *  y - the maximum value the product of xs and ys can assume
     */
    @Override
    public PolyCircuit buildTimesCircuit(PolyCircuit xs, PolyCircuit ys) {
        List<Formula<None>> zs = this.buildTimesCircuit(xs.getFormulae(), ys.getFormulae());
        BigInteger zsMax = xs.getMax().multiply(ys.getMax());
        if (zsMax.signum() == 0) {
            Formula<None> ff = this.formulaFactory.buildConstant(false);
            return new PolyCircuit(Collections.singletonList(ff), zsMax);
        }
        int zsMaxLength = zsMax.bitLength();
        for (int i = zs.size() - 1; i >= zsMaxLength; --i) {
            zs.remove(i);
        }
        return new PolyCircuit(zs, zsMax);
    }

    /**
     * @param xs - the first addend
     * @param ys - the second addend
     * @return a
     *  x - circuit for the sum of xs and ys<br>
     *  y - the maximum value the sum of xs and ys can assume
     */
    @Override
    public PolyCircuit buildPlusCircuit(PolyCircuit xs, PolyCircuit ys) {
        List<Formula<None>> zs = this.buildPlusCircuit(xs.getFormulae(), ys.getFormulae());
        BigInteger zsMax = xs.getMax().add(ys.getMax());
        if (zsMax.signum() == 0) {
            Formula<None> ff = this.formulaFactory.buildConstant(false);
            return new PolyCircuit(Collections.singletonList(ff), zsMax);
        }
        int zsMaxLength = zsMax.bitLength();
        for (int i = zs.size() - 1; i >= zsMaxLength; --i) {
            zs.remove(i);
        }
        return new PolyCircuit(zs, zsMax);
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
    public List<Formula<None>> buildTimesCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        // just consider the case that xs.size() >= ys.size(),
        // times is commutative :)
        if (xs.size() < ys.size()) {
            List<? extends Formula<None>> tmp = xs;
            xs = ys;
            ys = tmp;
        }

        int xsSize, ysSize;
        xsSize = xs.size();
        ysSize = ys.size();

        // this may look more involved than it actually is ...
        // idea: do not perform plus for the positions where you
        // would always have ZERO in written multiplication
        List<List<Formula<None>>> xAndYs = new ArrayList<List<Formula<None>>>(ysSize);
        for (int i = 0; i < ysSize; ++i) {
            Formula<None> y = ys.get(i);
            List<Formula<None>> addendI = new ArrayList<Formula<None>>(xsSize);
            for (int j = 0; j < xsSize; ++j) {
                Formula<None> x = xs.get(j);
                Formula<None> xAndY = this.formulaFactory.buildAnd(y, x);
                addendI.add(xAndY);
            }
            xAndYs.add(addendI);
        }

        List<Formula<None>> currentSumTuple, result;
        result = new ArrayList<Formula<None>>(xsSize + ysSize);
        currentSumTuple = xAndYs.get(0);
        result.add(currentSumTuple.get(0));
        currentSumTuple = currentSumTuple.subList(1, currentSumTuple.size());
        for (int i = 1; i < ysSize; ++i) {
            List<Formula<None>> currentAddend = xAndYs.get(i);
            currentSumTuple = this.actuallyBuildPlusCircuit(currentSumTuple, currentAddend);
            result.add(currentSumTuple.get(0));
            currentSumTuple = currentSumTuple.subList(1, currentSumTuple.size());
        }
        result.addAll(currentSumTuple);
        return result;
    }

    /**
     * Builds a circuit that has xs + ys as output, given xs and ys
     * as inputs.
     *
     * @param xs the first addend
     * @param ys the second addend
     * @return output of a circuit that encodes xs + ys given xs and
     *  ys as inputs
     */
    public List<Formula<None>> buildPlusCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {
        return this.actuallyBuildPlusCircuit(xs, ys);
    }

    /**
     * Builds a circuit that has xs + ys as output, given xs and ys
     * as inputs. Does the actual work.
     *
     * Does not get overwritten in subclasses that handle bounded
     * arithmetic. This is important because buildTimes uses buildPlus
     * also at higher argument positions.
     *
     * @param xs the first addend
     * @param ys the second addend
     * @return output of a circuit that encodes xs + ys given xs and
     *  ys as inputs
     */
    protected List<Formula<None>> actuallyBuildPlusCircuit(List<? extends Formula<None>> xs,
            List<? extends Formula<None>> ys) {

        List<Formula<None>> zs;
        zs = new ArrayList<Formula<None>>(xs.size() > ys.size() ? xs.size()+1 : ys.size()+1);

        // 3 cases:
        // 1) xs.size() == ys.size(), xs.size() == 1
        if (xs.size() == ys.size()) {
            int size = xs.size();
            if (size == 1) {
                List<Formula<None>> x0y0 = new ArrayList<Formula<None>>(2);
                x0y0.add(xs.get(0));
                x0y0.add(ys.get(0));
                Formula<None> z0, z1;
                z0 = this.formulaFactory.buildXor(x0y0);
                z1 = this.formulaFactory.buildAnd(x0y0); // share and enjoy.
                zs.add(z0);
                zs.add(z1);
            }
            else { // 2) xs.size() == ys.size() && xs.size() > 1
                Formula<None>[] carries = new Formula[size-1];
                List<Formula<None>> x0y0 = new ArrayList<Formula<None>>(2);
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
                Formula<None> zLast = this.build2or3Circuit(xs.get(size-1),
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
                List<? extends Formula<None>> tmp = xs;
                xs = ys;
                ys = tmp;
            }

            int xsSize, ysSize;
            xsSize = xs.size();
            ysSize = ys.size();

            Formula<None>[] carries = new Formula[ysSize-1];
            List<Formula<None>> x0y0 = new ArrayList<Formula<None>>(2);
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
            Formula<None> zLast = this.formulaFactory.buildAnd(ys.get(ysSize-1), carries[ysSize-2]);
            zs.add(zLast);
        }

        if (Globals.useAssertions) {
            assert zs.size() == 1 + Math.max(xs.size(), ys.size());
        }

        return zs;
    }

    @Override
    public PolyCircuit buildMinusCircuit(PolyCircuit xs, PolyCircuit ys) {
        throw new UnsupportedOperationException("Subtraction has not yet been implemented in this factory");
    }
}
