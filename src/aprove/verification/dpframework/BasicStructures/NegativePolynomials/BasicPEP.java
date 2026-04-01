/*
 * Created on 14.03.2005
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;


/**
 *
 * @author thiemann
 *
 * This class represents a partially evaluated Term w.r.t.
 * some Interpretation
 */
public abstract class BasicPEP {


    @Override
    public abstract int hashCode();
    @Override
    public abstract boolean equals(Object other);

    /**
     * returns the specialization of this pet wrt. the new interpretation for f
     * @param f
     * @param interpretation
     * @return
     */
    public abstract PEP specialize(FunctionSymbol f, int[] interpretation);

    /**
     * requires that this PEP is completely specified.
     * Then this method returns the eliminates all max-operators by
     * over-/under approximations.
     * @param left - If left is True, we obtain an underapproximation,
     *               otherwise we get an overapproximation.
     *               (the constraint s > t can be ensured by A_left(s) > A_right(t))
     * @return
     */
    public abstract PEP deMaximize(Boolean left);

    /**
     * returns the set of FunctionSymbols that are needed to fully
     * specify this pet
     * @return
     */
    public abstract Set<FunctionSymbol> getMissingInterpretations();

    public abstract PEVL createPEVL(boolean leftMode);
}
