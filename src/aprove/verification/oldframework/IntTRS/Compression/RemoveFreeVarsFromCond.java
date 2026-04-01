package aprove.verification.oldframework.IntTRS.Compression;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class RemoveFreeVarsFromCond {

    private IDPPredefinedMap predefinedMap;
    // if true, f(x) -> f(y) | y < x and similar conditions are not removed.
    private boolean retainRelationInformation;

    public RemoveFreeVarsFromCond(IDPPredefinedMap predefinedMap, boolean retainRelationInformation) {
        this.predefinedMap = predefinedMap;
        this.retainRelationInformation = retainRelationInformation;
    }

    public RemoveFreeVarsFromCond(boolean retainRelationInformation) {
        this(IDPPredefinedMap.DEFAULT_MAP, retainRelationInformation);
    }

    /**
     * @return a rule which does not use free variables in its conditions
     */
    public IGeneralizedRule removeFreeVarsFromCond(IGeneralizedRule rule) {
        final Collection<TRSVariable> boundVars = rule.getLeft().getVariables();
        boundVars.addAll(rule.getRight().getVariables());
        final TRSTerm cond = rule.getCondTerm();
        TRSTerm newCond = cond;

        if (newCond == null) {
            return rule;
        }

        boolean changedCond = false;
        do {
            changedCond = false;
            subtermSearch: for (final Pair<Position, TRSTerm> p : newCond.getPositionsWithSubTerms()) {
                final Position pos = p.x;
                final TRSTerm subterm = p.y;
                if (subterm instanceof TRSFunctionApplication) {
                    final TRSFunctionApplication fa = (TRSFunctionApplication) subterm;
                    final FunctionSymbol fs = fa.getRootSymbol();
                    if (!predefinedMap.isPredefined(fs)) {
                        continue;
                    }

                    for (int argNum = 0; argNum < fs.getArity(); argNum++) {
                        final TRSTerm arg = fa.getArgument(argNum);
                        if (!(arg instanceof TRSVariable)) {
                            continue;
                        }
                        if (boundVars.contains(arg)) {
                            continue;
                        }

                        final TRSTerm newTerm;
                        if (predefinedMap.isLand(fs)) {
                            //For and, we know this part can always be satisfied, so project on the other:
                            if (argNum == 0) {
                                newTerm = fa.getArgument(1);
                            } else {
                                newTerm = fa.getArgument(0);
                            }
                        } else if (retainRelationInformation
                            && (predefinedMap.isEq(fs)
                                || predefinedMap.isGe(fs)
                                || predefinedMap.isGt(fs)
                                || predefinedMap.isLe(fs)
                                || predefinedMap.isLt(fs) || predefinedMap.isNeq(fs)))
                        {
                            /*
                             * We have some relation x R y. If x is bound but y is not, we might still infer some
                             * information for y. As an example, y < x is useful information even if y is not bound.
                             */
                            continue;
                        } else {
                            /*
                             * For all others, we know it may be true,
                             * or not. Re-use the free variable,
                             */
                            newTerm = TRSTerm.createVariable(arg.getName() + "_" + pos.toString());
                        }
                        newCond = newCond.replaceAt(pos, newTerm);
                        changedCond = true;
                        break subtermSearch;
                    }
                } else if (pos.isEmptyPosition()) {
                    if (subterm instanceof TRSVariable && !boundVars.contains(subterm)) {
                        newCond = TRSTerm.createFunctionApplication(predefinedMap.getBooleanTrue().getSym());
                        changedCond = false;
                        break subtermSearch;
                    }
                }
            }
        } while (changedCond);
        return IGeneralizedRule.create(rule.getLeft(), rule.getRight(), newCond);
    }

}
