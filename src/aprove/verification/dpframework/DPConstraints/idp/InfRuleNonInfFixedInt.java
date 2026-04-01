/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

@Deprecated
public class InfRuleNonInfFixedInt extends InfRuleConstraintRepl<Object> {

    // FunctionSymbol -> <deterministic, varIgnoring>
    private final Map<FunctionSymbol, Triple<Boolean, Boolean[], CriticalPairs>> critPairsCache;

    public InfRuleNonInfFixedInt(Mode mode) {
        super(mode);
        this.critPairsCache = new LinkedHashMap<FunctionSymbol, Triple<Boolean, Boolean[], CriticalPairs>>();
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.FIXED_INT_CONST;
    }

    @Override
    public String getLongName() {
        return "InfRule Fixed Int: marks user defined functions that evaluate to exactly one int normal form that is independent of input";
    }

    @Override
    public String getName() {
        return "InfRule Fixed Int";
    }

    @Override
    protected Constraint processConstraint(
        Implication origImplication,
        Constraint constraint,
        boolean isConclusion,
        Object data,
        Abortion aborter) throws AbortionException
    {
        if (constraint.getTag(this.getID()) != null) {
            return constraint;
        }
        constraint.setTag(this.getID(), Boolean.TRUE);
        if (constraint.isReducesTo()) {
            ReducesTo reducesTo = (ReducesTo) constraint;
            if (reducesTo.getLeft().isVariable()) {
                return constraint;
            }
            TRSFunctionApplication lhs = (TRSFunctionApplication) reducesTo.getLeft();
            IDPPredefinedMap predefinedMap = ((IdpInductionCalculus) this.irc).getIdp().getRuleAnalysis().getPreDefinedMap();
            PredefinedFunction func = predefinedMap.getPredefinedFunction(lhs.getRootSymbol());
            if (reducesTo.getRight().isVariable()
                || ((TRSFunctionApplication) reducesTo.getRight()).getRootSymbol().equals(lhs.getRootSymbol())
                || func == null)
            {
                return constraint;
            }
            if (func.isRelation()) {
                ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(func.getArity());
                boolean changed = false;
                for (TRSTerm arg : lhs.getArguments()) {
                    TRSTerm newArg = this.processRelationArgument(arg, predefinedMap, aborter);
                    changed = changed | arg != newArg;
                    newArgs.add(newArg);
                }
                if (changed) {
                    return ReducesTo.create(
                        TRSTerm.createFunctionApplication(
                            lhs.getRootSymbol(),
                            ImmutableCreator.create(newArgs)),
                        reducesTo.getRight(),
                        null,
                        reducesTo.getCount(),
                        reducesTo.getId());
                } else {
                    return constraint;
                }
            } else {
                return constraint;
            }
        } else {
            return constraint;
        }
    }

    protected TRSTerm processRelationArgument(TRSTerm arg, IDPPredefinedMap predefinedMap, Abortion aborter)
        throws AbortionException
    {
        if (arg.isVariable()) {
            return arg;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) arg;
        FunctionSymbol fs = fa.getRootSymbol();
        if (predefinedMap.isInt(fs, DomainFactory.INTEGERS)) {
            return arg;
        }
        if (this.irc.isDefinedSymbol(fs)) {
            if (this.analyzeTerm(arg, predefinedMap, aborter)) {
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(1);
                args.add(arg);
                return TRSTerm.createFunctionApplication(
                    ((IdpNonInfIC) this.irc).getFixedIntConstant(),
                    ImmutableCreator.create(args));
            }
        }
        return arg;
    }

    protected boolean analyzeTerm(TRSTerm t, IDPPredefinedMap predefinedMap, Abortion aborter) throws AbortionException {
        if (t.isVariable()) {
            return false;
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication) t;
            FunctionSymbol fs = fa.getRootSymbol();
            PredefinedSemantics sem = predefinedMap.getPredefinedSemantics(fs);
            if (sem != null) {
                if (sem.isConstructor() || ((PredefinedFunction) sem).isArithmetic()) {
                    return true;
                } else {
                    return false;
                }
            }
            Triple<Boolean, Boolean[], CriticalPairs> fsAnalyzation = this.analyzeFs(fs, true, aborter);
            if (!fsAnalyzation.x) {
                return false;
            }
            // is an argument used that is not deterministic?
            for (int i = fsAnalyzation.y.length - 1; i >= 0; i--) {
                if (!fsAnalyzation.y[i] && !this.analyzeTerm(fa.getArgument(i), predefinedMap, aborter)) {
                    return false;
                }
            }
        }
        return true;
    }

    protected Triple<Boolean, Boolean[], CriticalPairs> analyzeFs(
        FunctionSymbol fs,
        boolean checkDeterminism,
        Abortion aborter) throws AbortionException
    {
        Triple<Boolean, Boolean[], CriticalPairs> cached = this.critPairsCache.get(fs);
        if (cached == null) {
            IdpNonInfIC ic = (IdpNonInfIC) this.getIrc();
            RuleAnalysis<GeneralizedRule> rRules = ic.getIdp().getRuleAnalysis().getRAnalysis();
            ImmutableSet<GeneralizedRule> fsRules = rRules.getRuleMap().get(fs);
            Boolean[] varIgnoring = new Boolean[fs.getArity()];
            if (fsRules != null) {
                Map<FunctionSymbol, Set<GeneralizedRule>> smallMap =
                    new LinkedHashMap<FunctionSymbol, Set<GeneralizedRule>>();
                smallMap.put(fs, fsRules);
                CriticalPairs criticalPairs = new CriticalPairs(fsRules, smallMap);
                // check for unused vars
                for (GeneralizedRule r : fsRules) {
                    TRSFunctionApplication lhs = r.getLeft();
                    Set<TRSVariable> rightVariables = r.getRight().getVariables();
                    for (int i = fs.getArity() - 1; i >= 0; i--) {
                        TRSTerm arg = lhs.getArgument(i);
                        varIgnoring[i] = !arg.isVariable() || !rightVariables.contains(arg);
                    }
                }
                cached = new Triple<Boolean, Boolean[], CriticalPairs>(null, varIgnoring, criticalPairs);
            } else {
                for (int i = fs.getArity() - 1; i >= 0; i--) {
                    varIgnoring[i] = true;
                }
                cached = new Triple<Boolean, Boolean[], CriticalPairs>(true, varIgnoring, null);
            }
            this.critPairsCache.put(fs, cached);
        }
        if (cached.x == null && checkDeterminism) {
            IdpNonInfIC ic = (IdpNonInfIC) this.getIrc();
            RuleAnalysis<GeneralizedRule> rRules = ic.getIdp().getRuleAnalysis().getRAnalysis();
            ImmutableSet<? extends GeneralizedRule> fsRules = rRules.getRuleMap().get(fs);
            boolean deterministic = true;
            if (cached.z.isNonOverlapping(aborter)) {
                Set<FunctionSymbol> usedSymbols = new LinkedHashSet<FunctionSymbol>();
                ruleLoop: for (GeneralizedRule r : fsRules) {
                    for (FunctionSymbol used : r.getRight().getFunctionSymbols()) {
                        if (usedSymbols.add(used)) {
                            Triple<Boolean, Boolean[], CriticalPairs> usedAnalysis = this.analyzeFs(used, false, aborter);
                            if (usedAnalysis.x != Boolean.TRUE && !usedAnalysis.z.isNonOverlapping(aborter)) {
                                deterministic = false;
                                break ruleLoop;
                            }
                        }
                    }
                }
                if (deterministic) {
                    for (FunctionSymbol used : usedSymbols) {
                        this.critPairsCache.get(used).x = true;
                    }
                }
            } else {
                deterministic = false;
            }
            cached.x = deterministic;
        }
        return cached;
    }

    @Override
    protected Object prepare(Implication implication, Abortion aborter) {
        // TODO Auto-generated method stub
        return null;
    }

}
