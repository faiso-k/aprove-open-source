package aprove.verification.complexity.LowerBounds.EquationalUnification;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Equation;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Given a pair s =? t, assume that there is an equation f(x1,...,xn) -> r s.t. the root symbol of s or t is f. Wlog
 * assume that the root symbol of s is f, s.t. we have s=f(y1,...,yn). Then (s, t) is replaced with the following pairs:
 * - xi =? yi for each i in {1,...,n}
 * - r =? t
 * Since there might be multiple such equations, multiple sets of new pairs may be returned.
 * @author ffrohn
 */
public class UnifyModuloEquation implements EquationalUnificationRule {

    private Iterable<Equation> equations;
    private RenamingCentral renamingCentral;
    private TrsTypes types;

    UnifyModuloEquation(Iterable<Equation> equations, RenamingCentral renamingCentral, TrsTypes types) {
        this.equations = equations;
        this.renamingCentral = renamingCentral;
        this.types = types;
    }

    @Override
    public Optional<Set<Result>> apply(TRSTerm s, TRSTerm t, UnificationProblem unificationProblem) {
        if (s.isVariable() || t.isVariable()) {
            return Optional.empty();
        }
        // Try to apply equations to s as well as t, if possible.
        List<Pair<TRSFunctionApplication, TRSTerm>> orientations = new ArrayList<>(2);
        orientations.add(new Pair<>((TRSFunctionApplication) s, t));
        if (t instanceof TRSFunctionApplication) {
            orientations.add(new Pair<>((TRSFunctionApplication) t, s));
        }
        Set<Result> result = new LinkedHashSet<>();
        for (Pair<TRSFunctionApplication, TRSTerm> toUnify : orientations) {
            TRSFunctionApplication func = toUnify.x;
            TRSTerm term = toUnify.y;
            // Look at each equational rule.
            for (Equation rule : this.equations) {
                // Check whether the root symbols are equal.
                if (func.getRootSymbol().equals(rule.getLeftRootSymbol())) {
                    Equation varRenamedRule = rule.renameVariables(this.renamingCentral, this.types);
                    UnificationProblem newProblem = new UnificationProblem();
                    // Add the new pairs for the arguments.
                    for (int i = 0; i < func.getRootSymbol().getArity(); i++) {
                        Position position = Position.create(i);
                        newProblem.add(varRenamedRule.getLeft().getSubterm(position), func.getSubterm(position));
                    }
                    // Add the new rule for the root position.
                    newProblem.add(varRenamedRule.getRight(), term);
                    result.add(new Result(newProblem));
                }
            }
        }
        if (result.isEmpty()) {
            return Optional.empty();
        } else {
            return Optional.of(result);
        }
    }

}
