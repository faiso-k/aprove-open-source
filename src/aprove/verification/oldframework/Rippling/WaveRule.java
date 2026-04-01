package aprove.verification.oldframework.Rippling;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.*;

public class WaveRule extends Rule {

    public static WaveRule create(AlgebraTerm left, AlgebraTerm right) {
        return new WaveRule(new Vector<Rule>(), left,right);
    }

    protected WaveRule(List<Rule> conds, AlgebraTerm left, AlgebraTerm right) {
        super(conds, left, right);
    }

    public WaveRule renameVariables(Set<AlgebraVariable> setOfVariables) {
        return this.renameVariables( new FreshVarGenerator(setOfVariables));
    }

    public WaveRule renameVariables(FreshVarGenerator freshVarGenerator) {

        AlgebraTerm leftCopy  = this.left.deepcopy();
        leftCopy.renameVars(freshVarGenerator);

        AlgebraTerm rightCopy = this.right.deepcopy();
        rightCopy.renameVars(freshVarGenerator);

        return WaveRule.create(leftCopy, rightCopy);

    }

    @Override
    public WaveRule deepcopy() {
        return (WaveRule)super.deepcopy();
    }

}
