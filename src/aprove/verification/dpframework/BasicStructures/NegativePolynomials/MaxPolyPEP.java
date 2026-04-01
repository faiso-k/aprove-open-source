/*
 * Created on 14.03.2005
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

public class MaxPolyPEP extends BasicPEP {

    private final PEP pep;

    private final int hashCode;

    MaxPolyPEP(PEP pet) {
        this.pep = pet;
        this.hashCode = this.pep.hashCode()*290230841+75290129;
    }

    @Override
    public PEP specialize(FunctionSymbol f, int[] interpretation) {
        PEP t = this.pep.specialize(f, interpretation);
        if (t.isNonNegative()) {
            return t;
        }
        return PEP.create(new MaxPolyPEP(t), true);
    }

    @Override
    public PEP deMaximize(Boolean left) {
        PEP newPet = this.pep.deMaximize(left);
        return newPet.deMaximizeTop(left);
    }

    @Override
    public Set<FunctionSymbol> getMissingInterpretations() {
        return this.pep.getMissingInterpretations();
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof MaxPolyPEP) {
            MaxPolyPEP mPep = (MaxPolyPEP) other;
            return mPep.pep.equals(this.pep);
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public String toString() {
        return "max("+this.pep+")";
    }

    @Override
    public PEVL createPEVL(boolean leftMode) {
        return this.pep.createPEVL(leftMode);
    }

}
