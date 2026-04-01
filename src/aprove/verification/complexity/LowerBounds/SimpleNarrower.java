package aprove.verification.complexity.LowerBounds;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Rule;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;


public class SimpleNarrower {

    public static Set<Rule> narrow(Set<Rule> rules, Set<Rule> toNarrow, boolean innermost, Abortion aborter) {
        Set<Rule> res = new LinkedHashSet<>();
        for (Rule todo : toNarrow) {
            Set<Position> positions = new TreeSet<>(new InnerMostPositionComparator());
            TRSTerm right = todo.getRight();
            positions.addAll(right.getPositions());
            Set<Position> narrowedPositions = new LinkedHashSet<>();
            OUTER: for (Position pi : positions) {
                aborter.checkAbortion();
                if (innermost) {
                    for (Position tau : narrowedPositions) {
                        if (pi.isPrefixOf(tau)) {
                            continue OUTER;
                        }
                    }
                }
                TRSTerm t = right.getSubterm(pi);
                if (!t.isVariable()) {
                    for (Rule r : rules) {
                        AbstractRule varRenamedRule = r.renameVariables(RenamingCentral.create(right.getVariables()));
                        TRSSubstitution unifier = t.getMGU(varRenamedRule.getLeft());
                        if (unifier != null) {
                            narrowedPositions.add(pi);
                            TRSFunctionApplication lhs = todo.getLeft().applySubstitution(unifier);
                            TRSTerm rhs = todo.getRight().replaceAt(pi, varRenamedRule.getRight()).applySubstitution(unifier);
                            res.add(new Rule(lhs, rhs));
                        }
                    }
                }
            }
        }
        return res;
    }

}
