/*
 * Created on 14.03.2005
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

public class UnEvaluatedPEP extends BasicPEP {

    private final FunctionSymbol f;
    private final PEP[] args;
    private final Set<FunctionSymbol> missInterpretations;
    private final int hashCode;
    private final boolean allowNegatives;

    private PEVL cacheLeft;
    private PEVL cacheRight;

    private UnEvaluatedPEP(FunctionSymbol f, PEP[] args, Set<FunctionSymbol> miss, Set<String> max, boolean allowNegative) {
        this.f = f;
        this.args = args;
        this.missInterpretations = miss;
        this.hashCode = f.hashCode()*34290123+Arrays.hashCode(args)*109290321+803121459;
        this.cacheLeft = null;
        this.cacheRight = null;
        this.allowNegatives = allowNegative;
    }

    public static UnEvaluatedPEP create(FunctionSymbol f, PEP[] args, boolean allowNegative) {
        Set<FunctionSymbol> miss = new LinkedHashSet<FunctionSymbol>();
        Set<String> max = new LinkedHashSet<String>();
        miss.add(f);
        for (PEP pep : args) {
            miss.addAll(pep.getMissingInterpretations());
        }
        return new UnEvaluatedPEP(f, args, miss, max, allowNegative);
    }

    @Override
    public PEP specialize(FunctionSymbol g, int[] interpretation) {
        if (this.f.equals(g)) {
            PEP newPep = PEP.create(interpretation[0], this.allowNegatives);
            int i = 1;
            for (PEP pep : this.args) {
                int coeff = interpretation[i];
                if (coeff > 0) {
                    newPep = newPep.add(pep.specialize(g, interpretation), coeff);
                }
                i++;
            }
            if (!this.allowNegatives || newPep.isNonNegative()) {
                return newPep;
            }
            return PEP.create(new MaxPolyPEP(newPep), true);
        } else {
            int n = this.args.length;
            PEP[] newArgs = new PEP[n];
            for (int i=0; i<n; i++) {
                newArgs[i] = this.args[i].specialize(g, interpretation);
            }
            return PEP.create(UnEvaluatedPEP.create(this.f, newArgs, this.allowNegatives), this.allowNegatives);
        }
    }

    @Override
    public PEP deMaximize(Boolean left) {
        throw new RuntimeException("Cannot de-maximize unevaluated PET");
    }

    @Override
    public Set<FunctionSymbol> getMissingInterpretations() {
        return this.missInterpretations;
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof UnEvaluatedPEP) {
            UnEvaluatedPEP uPet = (UnEvaluatedPEP) other;
            if (uPet.hashCode == this.hashCode && uPet.f.equals(this.f)) {
                return Arrays.equals(uPet.args, this.args);
            }
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }


    @Override
    public String toString() {
        String s = this.f.getName()+"(";
        boolean first = true;
        for (PEP pep : this.args) {
            if (first) {
                first = false;
            } else {
                s += ", ";
            }
            s += pep;
        }
        return s+")";
    }

    @Override
    public PEVL createPEVL(boolean leftMode) {
        if ((leftMode && this.cacheLeft == null) || (!leftMode && this.cacheRight == null)) {
            int n = this.args.length;
            PEVL[] args = new PEVL[n];
            int i = 0;
            for (PEP pep : this.args) {
                args[i] = pep.createPEVL(leftMode);
                i++;
            }
            PEVL pevl = PEVL.create(this.f, args, leftMode);
            if (leftMode) {
                this.cacheLeft = pevl;
            } else {
                this.cacheRight = pevl;
            }
            return pevl;
        } else {
            if (leftMode) {
                return this.cacheLeft;
            } else {
                return this.cacheRight;
            }
        }
    }

}
