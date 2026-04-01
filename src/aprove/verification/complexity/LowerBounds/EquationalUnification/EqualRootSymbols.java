package aprove.verification.complexity.LowerBounds.EquationalUnification;

import java.util.*;

import aprove.verification.complexity.LowerBounds.GeneratorEquations.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * [f(x1,...,xn) =? f(y1,...,yn)] -> [x1 =? y1,..., xn =? yn]
 * @author ffrohn
 */
public class EqualRootSymbols implements EquationalUnificationRule {

    private TermGenerator termGenerator;

    public EqualRootSymbols(TermGenerator termGenerator) {
        this.termGenerator = termGenerator;
    }

    @Override
    public Optional<Set<Result>> apply(TRSTerm s, TRSTerm t, UnificationProblem unificationProblem) throws NoUnifierException {
        if ((!s.isConstant() && PFHelper.isArithExp(s)) || (!t.isConstant() && PFHelper.isArithExp(t))) {
            return Optional.empty();
        }
        if (s instanceof TRSFunctionApplication && t instanceof TRSFunctionApplication) {
            TRSFunctionApplication sFunc = (TRSFunctionApplication) s;
            TRSFunctionApplication tFunc = (TRSFunctionApplication) t;
            if (sFunc.getRootSymbol().equals(tFunc.getRootSymbol())) {
                UnificationProblem result = new UnificationProblem();
                for (int i = 0; i < sFunc.getRootSymbol().getArity(); i++) {
                    Position position = Position.create(i);
                    result.add(sFunc.getSubterm(position), tFunc.getSubterm(position));
                }
                return Optional.of(Collections.singleton(new Result(result)));
            } else if (!termGenerator.isGeneratorSymbol(sFunc.getRootSymbol()) && !termGenerator.isGeneratorSymbol(tFunc.getRootSymbol()) ) {
                throw new NoUnifierException();
            }
        }
        return Optional.empty();
    }

}
