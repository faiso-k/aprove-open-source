/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Algorithms.Cap;

import java.util.*;

import aprove.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class ICap implements IECap {

    private static final ImmutableMap<IPosition, ImmutableSet<IRule>> EMPTY_SET_POS =
        ImmutableCreator.create(Collections.singletonMap(IPosition.create(),
            ImmutableCreator.create(Collections.<IRule> emptySet())));

    private final Map<Quadruple<RuleAnalysis<IRule>, IQTermSet, Set<? extends ITerm<?>>, ? extends ITerm<?>>, Pair<? extends ITerm<?>, ImmutableMap<IPosition, ImmutableSet<IRule>>>> cache;

    public ICap() {
        this.cache =
            new LinkedHashMap<Quadruple<RuleAnalysis<IRule>, IQTermSet, Set<? extends ITerm<?>>, ? extends ITerm<?>>, Pair<? extends ITerm<?>, ImmutableMap<IPosition, ImmutableSet<IRule>>>>();
    }

    @Override
    public <R extends SemiRing<R>> Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>> cap(final RuleAnalysis<IRule> rules,
        final IQTermSet q,
        final Set<? extends ITerm<?>> s,
        final ITerm<R> t,
        final IECap.ICapFreshNameGenerator freshNameGen,
        final boolean useCache,
        final boolean fillRules) {
        if (Globals.useAssertions) {
            // assert(t.checkVariablePrefix(ITerm.SECOND_STANDARD_PREFIX));
            assert (ICap.icapAssertCheck(q, rules.getRootToStandardLeftHandSides()));
        }
        if (useCache) {
            final Quadruple<RuleAnalysis<IRule>, IQTermSet, Set<? extends ITerm<?>>, ITerm<R>> cacheKey =
                new Quadruple<RuleAnalysis<IRule>, IQTermSet, Set<? extends ITerm<?>>, ITerm<R>>(
                    rules, q, s, t);
            @SuppressWarnings("unchecked")
            final Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>> cached =
                (Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>>) this.cache.get(cacheKey);
            if (cached != null) {
                return cached;
            }
        }
        final Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>> capRes =
            this.doCap(rules, q, q.canAllLhsBeRewritten(rules.getRules()), s, t,
                freshNameGen, useCache, fillRules);
        return capRes;
    }

    private <R extends SemiRing<R>> Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>> doCap(final RuleAnalysis<IRule> rules,
        final IQTermSet q,
        final boolean innermost,
        final Set<? extends ITerm<?>> S,
        final ITerm<R> t,
        final ICapFreshNameGenerator freshNameGen,
        final boolean useCache,
        final boolean fillRules) {
        Quadruple<RuleAnalysis<IRule>, IQTermSet, Set<? extends ITerm<?>>, ITerm<R>> cacheKey =
            null;
        if (useCache) {
            cacheKey =
                new Quadruple<RuleAnalysis<IRule>, IQTermSet, Set<? extends ITerm<?>>, ITerm<R>>(
                        rules, q, S, t);
            @SuppressWarnings("unchecked")
            final Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>> cached =
                (Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>>) this.cache.get(cacheKey);
            if (cached != null) {
                return cached;
            }
        }

        Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>> res = null;

        final Map<IPosition, ImmutableSet<IRule>> subPositions =
            new LinkedHashMap<IPosition, ImmutableSet<IRule>>();

        IFunctionApplication<R> capedT = null;

        final Set<IRule> applicableRules = new LinkedHashSet<IRule>();
        if (t.isVariable()) {
            if (innermost) {
                res =
                    new Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>>(
                            t, ICap.EMPTY_SET_POS);
            }
        } else {
            final IFunctionApplication<R> f = (IFunctionApplication<R>) t;
            // cap arguments
            final ArrayList<ITerm<?>> arguments =
                new ArrayList<ITerm<?>>(f.getRootSymbol().getArity());
            boolean changed = false;
            final int arity = f.getRootSymbol().getArity();
            for (int i = 0; i < arity; i++) {
                final Pair<? extends ITerm<?>, ImmutableMap<IPosition, ImmutableSet<IRule>>> capRes =
                    this.doCap(rules, q, innermost, S, f.getArgument(i),
                        freshNameGen, useCache, fillRules);
                arguments.add(capRes.x);
                if (!capRes.y.isEmpty()) {
                    changed = true;
                    for (final Map.Entry<IPosition, ImmutableSet<IRule>> e : capRes.y.entrySet()) {
                        subPositions.put(e.getKey().prepend(i), e.getValue());
                    }
                }
            }

            capedT =
                changed ? ITerm.createFunctionApplication(f.getRootSymbol(),
                    ImmutableCreator.create(arguments)) : f;
                // System.err.println("SUB CAP: " + t + " -> " + capedT );
                boolean ok = true;
                final Map<IVariable<?>, IVariable<?>> substMap =
                    new LinkedHashMap<IVariable<?>, IVariable<?>>();
                final IFunctionApplication<?> capedRenamedT =
                    capedT.renumberVariables(substMap, ITerm.THIRD_STANDARD_PREFIX,
                        0).x;
                final Set<ITerm<?>> renamedS = new LinkedHashSet<ITerm<?>>();
                final VarRenaming subst =
                    VarRenaming.create(ImmutableCreator.create(substMap), true, rules.getPolyFactory());
                for (final ITerm<?> s : S) {
                    renamedS.add(s.applySubstitution(subst));
                }
                final PredefinedFunction<?, R> func =
                    PredefinedUtil.getPredefinedFunction(capedT.getRootSymbol());
                if (func != null) {
                    // check predefined rules
                    // System.err.print("CAP: " + capedT + " " + func.canMatchPredefLhs(capedT) + " " );
                    if (func.canMatchPredefLhs(capedT)
                            && !q.canAlwaysRewritteAnArgUnifiedPredefLhs(capedT)) {
                        if (func.hasFiniteRuleSet()) {
                            final ImmutableSet<? extends IRule> funcRules =
                                func.getFiniteRuleSet(capedT.getRootSymbol());
                            checkRules: for (final IRule rule : funcRules) {
                                final IFunctionApplication<?> lhs =
                                    rule.getLhsInStandardRepresentation();
                                final ISubstitution mgu = lhs.getMGU(capedRenamedT);
                                if (mgu != null) {
                                    // check for non Q normal forms
                                    for (final ITerm<?> s : renamedS) {
                                        if (q.canBeRewritten(s.applySubstitution(mgu))) {
                                            continue checkRules;
                                        }
                                    }
                                    for (final ITerm<?> s : lhs.getArguments()) {
                                        if (q.canBeRewritten(s.applySubstitution(mgu))) {
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
                            final IRule rule =
                                func.getAbstractRule(capedT.getRootSymbol());
                            final IFunctionApplication<?> lhs =
                                rule.getLhsInStandardRepresentation();
                            if (lhs.unifies(capedRenamedT)) {
                                ok = false;
                                if (fillRules || useCache) {
                                    applicableRules.add(rule);
                                }
                            }
                        }
                        // FIXME: do we have to consider S (infinitely many instantiations...)
                        /*
                    checkS : for (ITerm<?> s : S) {
                    if (Q.canBeRewritten(s.applySubstitution(mgu))) {
                    ok = true;
                    break;
                    }
                    }*/
                    }
                    // System.err.println("RES: " + ok);
                } else {
                    // check explicit rules
                    final Set<IRule> aplicableRules =
                        rules.getRuleMap().get(capedRenamedT.getRootSymbol());
                    if (aplicableRules != null) {
                        checkRules: for (final IRule rule : aplicableRules) {
                            final IFunctionApplication<?> lhs =
                                rule.getLhsInStandardRepresentation();
                            final ISubstitution mgu = lhs.getMGU(capedRenamedT);
                            if (mgu != null) {
                                // System.err.println("mgu " + mgu + " to " + rule);
                                // check for non Q normal forms
                                for (final ITerm<?> s : renamedS) {
                                    if (q.canBeRewritten(s.applySubstitution(mgu))) {
                                        // System.err.println("saved by Q " + s.applySubstitution(mgu));
                                        continue checkRules;
                                    }
                                }
                                for (final ITerm<?> s : lhs.getArguments()) {
                                    if (q.canBeRewritten(s.applySubstitution(mgu))) {
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
                    res =
                        new Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>>(
                                capedT, ImmutableCreator.create(subPositions));
                }
        }
        if (res == null) {
            IVariable<R> newVar;
            if (t.isVariable()) {
                newVar =
                    freshNameGen.getNextFreshVariable(((IVariable<R>) t).getDomain());
            } else {
                newVar =
                    freshNameGen.getNextFreshVariable(((IFunctionApplication<R>) t).getRootSymbol().getResultDomain());
            }
            // we must introduce new variable
            res =
                new Pair<ITerm<R>, ImmutableMap<IPosition, ImmutableSet<IRule>>>(
                        newVar, ImmutableCreator.create(Collections.singletonMap(
                            IPosition.create(),
                            ImmutableCreator.create(applicableRules))));
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

    private static boolean icapAssertCheck(final IQTermSet Q,
        final ImmutableMap<IFunctionSymbol<?>, ImmutableSet<IFunctionApplication<?>>> lhsR) {
        /*
        for (Set<IFunctionApplication<?>> lhss : lhsR.values()) {
            for (IFunctionApplication<?> lhs : lhss) {
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
    public boolean equals(final Object other) {
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
