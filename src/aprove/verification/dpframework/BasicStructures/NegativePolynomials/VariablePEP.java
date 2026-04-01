/*
 * Created on 14.03.2005
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

public class VariablePEP extends BasicPEP {

    private final String var;
    private static final Set<FunctionSymbol> missInterpretations = new LinkedHashSet<FunctionSymbol>();

    private final int hashCode;

    private VariablePEP(String var) {
        this.var = var;
        this.hashCode = var.hashCode()*3219023+32901205;
    }

    public static VariablePEP create(String var) {
        return new VariablePEP(var);
    }

    @Override
    public PEP specialize(FunctionSymbol f, int[] interpretation) {
        throw new RuntimeException("Cannot specialize variable!");
    }

    @Override
    public PEP deMaximize(Boolean left) {
        return PEP.create(this, true);
    }

    @Override
    public Set<FunctionSymbol> getMissingInterpretations() {
        return VariablePEP.missInterpretations;
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof VariablePEP) {
            VariablePEP vPep = (VariablePEP) other;
            return vPep.var.equals(this.var);
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
        return this.var;
    }

    @Override
    public PEVL createPEVL(boolean leftMode) {
        return PEVL.create(this.var, leftMode);
    }

}
