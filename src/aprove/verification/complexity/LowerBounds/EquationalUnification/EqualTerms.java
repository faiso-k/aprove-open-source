package aprove.verification.complexity.LowerBounds.EquationalUnification;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * [t =? t] -> []
 * @author ffrohn
 */
public class EqualTerms implements EquationalUnificationRule {

    @Override
    public Optional<Set<Result>> apply(TRSTerm s, TRSTerm t, UnificationProblem unificationProblem) {
        if (s.equals(t)) {
            return Optional.of(Collections.emptySet());
        } else {
            return Optional.empty();
        }
    }
}
