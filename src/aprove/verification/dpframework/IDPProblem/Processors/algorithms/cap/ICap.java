/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;


public class ICap implements IECap {

    public static final Integer SUB_SUB_TYPE = Integer.valueOf(0);

    private static final ImmutableMap<Position, ImmutableSet<GeneralizedRule>> EMPTY_SET_POS = ImmutableCreator.create(Collections.singletonMap(Position.create(), ImmutableCreator.create(Collections.<GeneralizedRule>emptySet())));

    private final Map<Triple<IDPRuleAnalysis, Set<? extends TRSTerm>, TRSTerm>, Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>>> cache;

    public ICap () {
        this.cache = new LinkedHashMap<Triple<IDPRuleAnalysis, Set<? extends TRSTerm>, TRSTerm>, Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>>>();
    }

    @Override
    public Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> cap(IDPRuleAnalysis ruleAnalysis,
            Set<? extends TRSTerm> s, TRSTerm t, ICapFreshNameGenerator freshNameGen, boolean useCache, boolean fillRules) {
        if (Globals.useAssertions) {
            // assert(t.checkVariablePrefix(Term.SECOND_STANDARD_PREFIX));
            assert (ICap.icapAssertCheck(ruleAnalysis.getQ(), ruleAnalysis.getRAnalysis().getRootToStandardLeftHandSides()));
        }
        Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> capRes = this.doCap(ruleAnalysis, s, t, freshNameGen, useCache, fillRules);
        return capRes;
    }

    private Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> doCap(IDPRuleAnalysis ruleAnalysis,
            Set<? extends TRSTerm> S, TRSTerm t, ICapFreshNameGenerator freshNameGen, boolean useCache, boolean fillRules) {
        Triple<IDPRuleAnalysis, Set<? extends TRSTerm>, TRSTerm> cacheKey = null;
        if (useCache) {
            cacheKey = new Triple<IDPRuleAnalysis, Set<? extends TRSTerm>, TRSTerm>(ruleAnalysis, S, t);
            Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> cached = this.cache.get(cacheKey);
            if (cached != null) {
                return cached;
            }
        }
        Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> res = null;
        Map<Position, ImmutableSet<GeneralizedRule>> subPositions = new LinkedHashMap<Position, ImmutableSet<GeneralizedRule>>();
        TRSFunctionApplication capedT = null;
        Set<GeneralizedRule> applicableRules = new LinkedHashSet<GeneralizedRule>();
        if (t.isVariable()) {
            if (ruleAnalysis.isNfQSubsetEqNfR()) {
                res = new Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>>(t, ICap.EMPTY_SET_POS);
            }
        } else {
            TRSFunctionApplication f = (TRSFunctionApplication) t;
            // cap arguments
            ArrayList<TRSTerm> arguments = new ArrayList<TRSTerm>(f.getRootSymbol().getArity());
            boolean changed = false;
            int arity = f.getRootSymbol().getArity();
            for (int i = 0; i < arity; i++) {
                Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>> capRes = this.doCap(ruleAnalysis, S, f.getArgument(i), freshNameGen, useCache, fillRules);
                arguments.add(capRes.x);
                if (!capRes.y.isEmpty()) {
                    changed = true;
                    for (Map.Entry<Position, ImmutableSet<GeneralizedRule>> e : capRes.y.entrySet()) {
                        subPositions.put(e.getKey().prepend(i), e.getValue());
                    }
                }
            }

            capedT = changed ? TRSTerm.createFunctionApplication(f.getRootSymbol(), ImmutableCreator.create(arguments)) : f;
            // System.err.println("SUB CAP: " + t + " -> " + capedT );
            boolean ok = true;
            IQTermSet Q = ruleAnalysis.getQ();
            IDPPredefinedMap predefinedMap = ruleAnalysis.getPreDefinedMap();
            Map<TRSVariable, TRSVariable> substMap = new LinkedHashMap<TRSVariable, TRSVariable>();
            TRSFunctionApplication capedRenamedT = capedT.renumberVariables(substMap, TRSTerm.THIRD_STANDARD_PREFIX, 0).x;
            Set<TRSTerm> renamedS = new LinkedHashSet<TRSTerm>();
            TRSSubstitution subst = TRSSubstitution.create(ImmutableCreator.create(substMap));
            for (TRSTerm s : S) {
                renamedS.add(s.applySubstitution(subst));
            }
            PredefinedFunction func = ruleAnalysis.getPreDefinedMap().getPredefinedFunction(capedT.getRootSymbol());
            if (func != null) {
                // check predefined rules
                // System.err.print("CAP: " + capedT + " " + func.canMatchPredefLhs(capedT) + " " );
                if (func.canMatchPredefLhs(capedT, predefinedMap) && !Q.canAlwaysRewritteAnArgUnifiedPredefLhs(capedT)) {
                    if (func.hasFiniteRuleSet()) {
                        ImmutableSet<GeneralizedRule> rules = func.getFiniteRuleSet(capedT.getRootSymbol());
                        checkRules: for (GeneralizedRule rule : rules) {
                            TRSFunctionApplication lhs = rule.getLhsInStandardRepresentation();
                            TRSSubstitution mgu = lhs.getMGU(capedRenamedT);
                            if (mgu != null) {
                                // check for non Q normal forms
                                for (TRSTerm s : renamedS) {
                                    if (Q.canBeRewritten(s.applySubstitution(mgu))) {
                                        continue checkRules;
                                    }
                                }
                                for (TRSTerm s : lhs.getArguments()) {
                                    if (Q.canBeRewritten(s.applySubstitution(mgu))) {
                                        continue checkRules;
                                    }
                                }
                                ok = false;
                                if (fillRules || useCache) {
                                    applicableRules.add(rule);
                                } else {
                                    break;
                                }
                            }
                        }
                    } else {
                        GeneralizedRule rule = func.getAbstractRule(capedT.getRootSymbol());
                        TRSFunctionApplication lhs = rule.getLhsInStandardRepresentation();
                        if (lhs.unifies(capedRenamedT)) {
                            ok = false;
                            if (fillRules || useCache) {
                                applicableRules.add(rule);
                            }
                        }
                    }
                    // FIXME: do we have to consider S (infinitely many instantiations...)
                    /*
                    checkS : for (Term s : S) {
                        if (Q.canBeRewritten(s.applySubstitution(mgu))) {
                            ok = true;
                            break;
                        }
                    }*/
                }
                // System.err.println("RES: " + ok);
            } else {
                // check explicit rules
                Set<GeneralizedRule> rules = ruleAnalysis.getRAnalysis().getRuleMap().get(capedRenamedT.getRootSymbol());
                if (rules != null) {
                    checkRules: for (GeneralizedRule rule : rules) {
                        TRSFunctionApplication lhs = rule.getLhsInStandardRepresentation();
                        TRSSubstitution mgu = lhs.getMGU(capedRenamedT);
                        if (mgu != null) {
                            // System.err.println("mgu " + mgu + " to " + rule);
                            // check for non Q normal forms
                            for (TRSTerm s : renamedS) {
                                if (Q.canBeRewritten(s.applySubstitution(mgu))) {
                                    // System.err.println("saved by Q " + s.applySubstitution(mgu));
                                    continue checkRules;
                                }
                            }
                            for (TRSTerm s : lhs.getArguments()) {
                                if (Q.canBeRewritten(s.applySubstitution(mgu))) {
                                    // System.err.println("mgu to " + s);
                                    continue checkRules;
                                }
                            }
                            ok = false;
                            if (fillRules || useCache) {
                                applicableRules.add(rule);
                            } else {
                                break;
                            }
                        }
                    }
                }
            }
            if (ok) {
                // no applicable rule
                res = new Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>>(capedT, ImmutableCreator.create(subPositions));
            }
        }
        if (res == null) {
            // we must introduce new variable
            TRSVariable newVar = freshNameGen.getNextFreshVariable();
            res = new Pair<TRSTerm, ImmutableMap<Position, ImmutableSet<GeneralizedRule>>>(newVar, ImmutableCreator.create(Collections.singletonMap(Position.create(), ImmutableCreator.create(applicableRules))));
        }
        if (useCache) {
            this.cache.put(cacheKey, res);
        }
        return res;
    }

    @Override
    public String getDescription() {
        return "ICap";
    }

    private static boolean icapAssertCheck(SimpleQTermSet Q, ImmutableMap<FunctionSymbol, ImmutableSet<TRSFunctionApplication>> lhsR) {
        /*
        for (Set<FunctionApplication> lhss : lhsR.values()) {
            for (FunctionApplication lhs : lhss) {
                // check that we really have Q normal implies R normal
                if (!Q.canBeRewritten(lhs)) {
                    return false;
                }
            }
        }*/
        return true;
    }

    @Override
    public Estimation getEstimation() {
        return IECap.Estimation.ICAP;
    }

    @Override
    public int hashCode() {
        return IECap.Estimation.ICAP.hashCode();
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other == null) {
            return false;
        }
        if (other.getClass() != this.getClass()) {
            return false;
        }
        return IECap.Estimation.ICAP.equals(((IECap) other).getEstimation());
    }
}
