/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.utility;

import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class FunctionAnalysis implements Immutable {

    private final boolean isConstant;
    private final ImmutableMap<Integer, RelDependency> dependencies;
    private final ImmutableSet<Integer> projectionPos;
    private final ImmutableSet<ImmutablePair<ImmutableSet<Integer>, Boolean>> posCombinations;
    private final FunctionSymbol fs;

    /**
     * @param isConstant - ignores variables
     * @param dependencies - increasing: x +1, decreasing: x - 1, independent: ignores x, wild x + 1, x - 1 or something user-defined with x
     * @param projectionPos - is a projection to x_i: f(t_1, ..., t_n) -> x_i is a rule for f
     * @param posCombinations - f(s_1, ..., s_n) -> g(s_1, ..., s_m), then set x:V(g(s_1, ..., s_m)) + y:true iff g is only arithmetic
     */
    public FunctionAnalysis (FunctionSymbol fs, boolean isConstant, ImmutableMap<Integer, RelDependency> dependencies, ImmutableSet<Integer> projectionPos, ImmutableSet<ImmutablePair<ImmutableSet<Integer>, Boolean>> posCombinations) {
        this.fs = fs;
        this.isConstant = isConstant;
        this.dependencies = dependencies;
        this.projectionPos = projectionPos;
        this.posCombinations = posCombinations;
    }

    protected boolean isConstant() {
        return this.isConstant;
    }

    protected boolean isProjection() {
        return !this.projectionPos.isEmpty();
    }

    public ImmutableMap<Integer, RelDependency> getDependencies() {
        return this.dependencies;
    }

    public ImmutableSet<Integer> getProjectionPos() {
        return this.projectionPos;
    }

    public ImmutableSet<ImmutablePair<ImmutableSet<Integer>, Boolean>> getPosCombinations() {
        return this.posCombinations;
    }

    public FunctionSymbol getFs() {
        return this.fs;
    }
}
