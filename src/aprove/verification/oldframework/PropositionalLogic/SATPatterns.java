package aprove.verification.oldframework.PropositionalLogic;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.Utility.*;

public class SATPatterns<T> {

    private Constant<T> ZERO, ONE;
    private FormulaFactory<T> formulaFactory;
    private boolean forceNonLinear;

    public SATPatterns(FormulaFactory<T> formulaFactory) {
        this(formulaFactory, false);
    }
    public SATPatterns(FormulaFactory<T> formulaFactory, boolean forceNonLinear) {
        this.formulaFactory = formulaFactory;
        this.ZERO = this.formulaFactory.buildConstant(false);
        this.ONE = this.formulaFactory.buildConstant(true);
        this.forceNonLinear = forceNonLinear;
    }
    public Formula<T> encodeExactlyOne(Formula<T>[] vars) {
        switch (vars.length) {
        case 0:
            return this.ZERO;
        case 1:
            return vars[0];
        }
        if (this.forceNonLinear) {
            List<Formula<T>> dArgs = new ArrayList<Formula<T>>();
            Formula<T>[] negVars = new Formula[vars.length];
            for (int i = 0; i < vars.length; i++) {
                negVars[i] = this.formulaFactory.buildNot(vars[i]);
            }
            for (int i = 0; i < vars.length; i++) {
                List<Formula<T>> args = new ArrayList<Formula<T>>();
                args.add(vars[i]);
                for (int j = 0; j < i; j++) {
                    args.add(negVars[j]);
                }
                for (int j = i+1; j < vars.length; j++) {
                    args.add(negVars[j]);
                }
                dArgs.add(this.formulaFactory.buildAnd(args));
            }
            return this.formulaFactory.buildOr(dArgs);
        }
        return this.encodeNTrue(new Formula[] {this.ZERO, this.ONE, this.ZERO}, vars);
    }
    public Formula<T> encodeExactlyOne(List<? extends Formula<T>> vars) {
        Formula<T> varsArray[] = new Formula[vars.size()];
        vars.toArray(varsArray);
        return this.encodeExactlyOne(varsArray);
    }
    public Formula<T> encodeAtMostOne(Formula<T>[] vars) {
        if (this.forceNonLinear) {
            List<Formula<T>> dArgs = new ArrayList<Formula<T>>();
            Formula<T>[] negVars = new Formula[vars.length];
            List<Formula<T>> args = new ArrayList<Formula<T>>();
            for (int i = 0; i < vars.length; i++) {
                negVars[i] = this.formulaFactory.buildNot(vars[i]);
                args.add(negVars[i]);
            }
            dArgs.add(this.formulaFactory.buildAnd(args));
            for (int i = 0; i < vars.length; i++) {
                args = new ArrayList<Formula<T>>();
                args.add(vars[i]);
                for (int j = 0; j < i; j++) {
                    args.add(negVars[j]);
                }
                for (int j = i+1; j < vars.length; j++) {
                    args.add(negVars[j]);
                }
                dArgs.add(this.formulaFactory.buildAnd(args));
            }
            return this.formulaFactory.buildOr(dArgs);
        }
        return this.encodeNTrue(new Formula[] {this.ONE, this.ONE, this.ZERO}, vars);
    }
    public Formula<T> encodeAtMostOne(List<? extends Formula<T>> vars) {
        Formula<T> varsArray[] = new Formula[vars.size()];
        vars.toArray(varsArray);
        return this.encodeAtMostOne(varsArray);
    }
    public Formula<T> encodeZeroOrTwo(Formula<T>[] vars) {
        return this.encodeNTrue(new Formula[] {this.ONE, this.ZERO, this.ONE, this.ZERO}, vars);
    }
    public Formula<T> encodeZeroOrTwo(List<? extends Formula<T>> vars) {
        Formula<T> varsArray[] = new Formula[vars.size()];
        vars.toArray(varsArray);
        return this.encodeZeroOrTwo(varsArray);
    }
    public Formula<T> encodeExactlyTwo(Formula<T>[] vars) {
        return this.encodeNTrue(new Formula[] {this.ZERO, this.ZERO, this.ONE, this.ZERO}, vars);
    }
    public Formula<T> encodeExactlyTwo(List<? extends Formula<T>> vars) {
        Formula<T> varsArray[] = new Formula[vars.size()];
        vars.toArray(varsArray);
        return this.encodeExactlyTwo(varsArray);
    }
    public Formula<T> encodeAtMostTwo(Formula<T>[] vars) {
        return this.encodeNTrue(new Formula[] {this.ONE, this.ONE, this.ONE, this.ZERO}, vars);
    }
    public Formula<T> encodeAtMostTwo(List<? extends Formula<T>> vars) {
        Formula<T> varsArray[] = new Formula[vars.size()];
        vars.toArray(varsArray);
        return this.encodeAtMostTwo(varsArray);
    }
    public Formula<T> encodeNTrue(Formula<T>[] fs, Formula<T>[] vars) {
        for (int i = 0; i < vars.length; i++) {
            Formula<T> x= vars[i];
             Formula<T> notX = this.formulaFactory.buildNot(x);
            for (int j = 0; j+1 < fs.length; j++) {
                Formula<T> f1 = this.formulaFactory.buildAnd(notX, fs[j]);
                Formula<T> f2 = this.formulaFactory.buildAnd(x, fs[j+1]);
                // optimize by restricting j to those that are still needed
                fs[j] = this.formulaFactory.buildOr(f1,f2);
            }
        }
        return fs[0];
    }
    public Formula<T> encodeSome(Formula<T>[] vars) {
        List<Formula<T>> args = new ArrayList<Formula<T>>(vars.length);
        for (int i = 0; i < vars.length; i++) {
            args.add(vars[i]);
        }
        return this.formulaFactory.buildOr(args);
    }
    public Formula<T> encodeSome(List<? extends Formula<T>> vars) {
        Formula<T> varsArray[] = new Formula[vars.size()];
        vars.toArray(varsArray);
        return this.encodeSome(varsArray);
    }
    public Formula<T> encodeNone(Formula<T>[] vars) {
        return this.formulaFactory.buildNot(this.encodeSome(vars));
    }
    public Formula<T> encodeNone(List<? extends Formula<T>> vars) {
        Formula<T> varsArray[] = new Formula[vars.size()];
        vars.toArray(varsArray);
        return this.encodeNone(varsArray);
    }

    /**
     * @param fmlae
     * @return a formula that encodes that an odd number of elements
     *  of fmlae is satisfied
     */
    public Formula<T> encodeOdd(List<Formula<T>> fmlae) {
        int size = fmlae.size();
        switch (size) {
        case 0:
            return this.ZERO;
        case 1:
            return fmlae.get(0);
        default:
            Formula<T> result;
            List<Formula<T>> args;
            args = new ArrayList<Formula<T>>(2);
            args.add(fmlae.get(0));
            args.add(fmlae.get(1));
            result = this.formulaFactory.buildXor(args);
            for (int i = 2; i < size; ++i) {
                args = new ArrayList<Formula<T>>(2);
                args.add(result);
                args.add(fmlae.get(i));
                result = this.formulaFactory.buildXor(args);
            }
            return result;
        }
    }


    /**
     * @param xs non-null, but possibly empty
     * @param ys non-null, but possibly empty
     * @return a formula which is satisfied iff at least as many elements of xs
     *  are satisfied as elements of ys
     */
    public Formula<T> encodeXsAtLeastAsManyTrueAsYs(List<Formula<T>> xs,
            List<Formula<T>> ys) {
        int xsSize = xs.size();
        int ysSize = ys.size();

        Formula<T> result;
        if (ysSize == 0) {
            // statement holds regardless of xs
            result = this.ONE;
        }
        else if (xsSize == 0) {
            // no y may become true
            Formula<T> someY = this.formulaFactory.buildOr(ys);
            result = this.formulaFactory.buildNot(someY);
        }
        else {
            // xsSize > 0 and ysSize > 0
            List<Formula<T>> xsSum = this.sumUp(xs);
            List<Formula<T>> ysSum = this.sumUp(ys);
            result = this.buildGECircuit(xsSum, ysSum);
        }
        return result;
    }

    /**
     * @param xs - non-null; consists of "bits" that are to be summed up
     *  to a bit-vector
     * @return List of formulas whose /binary value/ amounts to how many of xs
     *  have become true by the interpretation found by the SAT solver
     */
    public List<Formula<T>> sumUp(Collection<Formula<T>> xs) {
        if (xs.isEmpty()) {
            return Collections.<Formula<T>>singletonList(this.ZERO);
        }

        Iterator<? extends Formula<T>> xsIter = xs.iterator();
        Formula<T> x = xsIter.next();
        List<Formula<T>> xsSum = Collections.singletonList(x);
        int maxX = 1;
        while (xsIter.hasNext()) {
            x = xsIter.next();
            xsSum = this.buildPlus(xsSum, Collections.singletonList(x));

            // only use as many bits as necessary to represent the current sum
            ++maxX;
            int maxLength = AProVEMath.binaryLength(maxX);
            for (int i = xsSum.size() - 1; i >= maxLength; --i) {
                xsSum.remove(i);
            }
        }
        return xsSum;
    }

    /**
     * Builds a circuit that has xs + ys as output, given xs and ys
     * as inputs.
     *
     * Shamelessly taken and adapted from ArithmeticCircuitFactory.
     *
     * @param xs the first addend, non-empty
     * @param ys ths second addend, non-empty
     * @return output of a circuit that encodes xs + ys given xs and
     *  ys as inputs
     */
    public List<Formula<T>> buildPlus(List<? extends Formula<T>> xs,
            List<? extends Formula<T>> ys) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        List<Formula<T>> zs;
        zs = new ArrayList<Formula<T>>(xs.size() > ys.size() ? xs.size()+1 : ys.size()+1);

        // 3 cases:
        // 1) xs.size() == ys.size(), xs.size() == 1
        if (xs.size() == ys.size()) {
            int size = xs.size();
            if (size == 1) {
                List<Formula<T>> x0y0 = new ArrayList<Formula<T>>(2);
                x0y0.add(xs.get(0));
                x0y0.add(ys.get(0));
                Formula<T> z0, z1;
                z0 = this.formulaFactory.buildXor(x0y0);
                z1 = this.formulaFactory.buildAnd(x0y0); // share and enjoy.
                zs.add(z0);
                zs.add(z1);
            }
            else { // 2) xs.size() == ys.size() && xs.size() > 1
                Formula<T>[] carries = new Formula[size-1];
                List<Formula<T>> x0y0 = new ArrayList<Formula<T>>(2);
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
                Formula<T> z0;
                z0 = this.formulaFactory.buildXor(x0y0);
                zs.add(z0);
                for (int i = 1; i < size; ++i) {
                    Formula<T> zI;
                    zI = this.formulaFactory.buildXor(xs.get(i), ys.get(i), carries[i-1]);
                    zs.add(zI);
                }
                Formula<T> zLast = this.build2or3Circuit(xs.get(size-1),
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
                List<? extends Formula<T>> tmp = xs;
                xs = ys;
                ys = tmp;
            }

            int xsSize, ysSize;
            xsSize = xs.size();
            ysSize = ys.size();

            Formula<T>[] carries = new Formula[ysSize-1];
            List<Formula<T>> x0y0 = new ArrayList<Formula<T>>(2);
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
            Formula<T> zLast = this.formulaFactory.buildAnd(ys.get(ysSize-1), carries[ysSize-2]);
            zs.add(zLast);
        }

        if (Globals.useAssertions) {
            assert zs.size() == 1 + Math.max(xs.size(), ys.size());
        }
        return zs;
    }

    /**
     * @param f1
     * @param f2
     * @param f3
     * @return a formula/circuit which is satisfied by exactly those
     *  interpretations that satisfy at least 2 of the arguments
     */
    public Formula<T> build2or3Circuit(Formula<T> f1,
            Formula<T> f2, Formula<T> f3) {
        Formula<T> pos0, pos1, pos2;
        pos0 = this.formulaFactory.buildOr(f1, f2);
        pos1 = this.formulaFactory.buildOr(f1, f3);
        pos2 = this.formulaFactory.buildOr(f2, f3);
        return this.formulaFactory.buildAnd(pos0, pos1, pos2);
    }

    /**
     * Builds a Boolean circuit that encodes that xs represents
     * the same number as or a greater number than ys.
     *
     * Shamelessly taken and adapted from ArithmeticCircuitFactory.
     *
     * @param xs non-empty
     * @param ys non-empty
     * @return a formula that encodes that xs >= ys
     */
    public Formula<T> buildGECircuit(List<? extends Formula<T>> xs,
            List<? extends Formula<T>> ys) {
        if (Globals.useAssertions) {
            assert(! xs.isEmpty());
            assert(! ys.isEmpty());
        }

        int xsSize = xs.size();
        int ysSize = ys.size();

        // Codish style.
        Formula<T> result;
        if (xsSize == 1 && ysSize == 1) {
            result = this.formulaFactory.buildOr(xs.get(0),
                    this.formulaFactory.buildNot(ys.get(0)));
        }
        else if (xsSize > ysSize) {
            List<Formula<T>> args = new ArrayList<Formula<T>>(1+xsSize-ysSize);
            for (int i = ysSize; i < xsSize; ++i) {
                args.add(xs.get(i));
            }
            List<Formula<T>> newXs = new ArrayList<Formula<T>>(ysSize);
            for (int i = 0; i < ysSize; ++i) {
                newXs.add(xs.get(i));
            }
            args.add(this.buildGECircuit(/*xs.subList(0, ysSize)*/newXs, ys));
            result = this.formulaFactory.buildOr(args);
        }
        else if (xsSize < ysSize) {
            List<Formula<T>> args = new ArrayList<Formula<T>>(1+ysSize-xsSize);
            for (int i = xsSize; i < ysSize; ++i) {
                args.add(this.formulaFactory.buildNot(ys.get(i)));
            }
            List<Formula<T>> newYs = new ArrayList<Formula<T>>(xsSize);
            for (int i = 0; i < xsSize; ++i) {
                newYs.add(ys.get(i));
            }
            args.add(this.buildGECircuit(xs, /*ys.subList(0, xsSize)*/newYs));
            result = this.formulaFactory.buildAnd(args);
        }
        else { // xsSize == ysSize, xsSize != 1
            Formula<T> lastX = xs.get(xsSize - 1);
            Formula<T> lastY = ys.get(ysSize - 1);
            Formula<T> leftDisjunct = this.formulaFactory.buildAnd(lastX,
                    this.formulaFactory.buildNot(lastY));

            Formula<T> eqConjunct;
            eqConjunct = this.formulaFactory.buildIff(lastX, lastY);
            List<Formula<T>> newXs, newYs;
            newXs = new ArrayList<Formula<T>>(xsSize-1);
            newYs = new ArrayList<Formula<T>>(xsSize-1);
            for (int i = 0; i < xsSize - 1; ++i) {
                newXs.add(xs.get(i));
                newYs.add(ys.get(i));
            }
            Formula<T> recursivelyBuiltConjunct = this.buildGECircuit(/*xs.subList(0, xsSize-1)*/newXs, /*ys.subList(0, ysSize-1)*/newYs);
            Formula<T> rightDisjunct = this.formulaFactory.buildAnd(eqConjunct, recursivelyBuiltConjunct);
            result = this.formulaFactory.buildOr(leftDisjunct, rightDisjunct);
        }
        return result;
    }
}
