package aprove.verification.complexity.LowerBounds.EquationalUnification;

import java.util.*;

import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * [x =? t, e_1, ..., e_n] -> [x =? t, e_1{x/t}, ..., e_n{x/t}] if x does not occur in t, but in some e_i.
 * @author ffrohn
 */
public class ATermIsVariable implements EquationalUnificationRule {

    @Override
    public Optional<Set<Result>> apply(TRSTerm s, TRSTerm t, UnificationProblem unificationProblem) throws NoUnifierException {
        TRSVariable var;
        TRSTerm term;
        if (s.isVariable()) {
            var = (TRSVariable) s;
            term = t;
        } else if (t.isVariable()) {
            var = (TRSVariable) t;
            term = s;
        } else {
            return Optional.empty();
        }
        if (term.hasSubterm(var)) {
            if (PFHelper.isArithExp(term)) {
                return Optional.empty();
            } else {
                throw new NoUnifierException();
            }
        }
        if (!unificationProblem.isAssigned(var)) {
            return Optional.of(Collections.singleton(new Result(TRSSubstitution.create(var, term), new UnificationProblem(var, term))));
        } else {
            return Optional.empty();
        }
    }

}
