package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.TermTransitionPair;

import java.util.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.TermRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;


public class TermTransitionPairsSet {

    final private ImmutableSet<TermTransitionPair> transPairs;

    private TermTransitionPairsSet(final Collection<TermTransitionPair> transPairs) {
        this.transPairs = ImmutableCreator.create(new HashSet<>(transPairs));
    }


    public static TermTransitionPairsSet create(final Collection<TermTransitionPair> transPairs) {
        return new TermTransitionPairsSet(transPairs);
    }

    public static TermTransitionPairsSet create(final TermTransitionPair transPairs) {
        return TermTransitionPairsSet.create(Arrays.asList(transPairs));
    }

    public ImmutableSet<TermTransitionPair> getTransitionsPairs() {
        return this.transPairs;
    }

    public TermTransitionPairsSet remove(final TermTransitionPair transPair) {
        final Set<TermTransitionPair> transPairsRem = new HashSet<>();

        transPairsRem.addAll(this.transPairs);
        transPairsRem.remove(transPair);

        return TermTransitionPairsSet.create(transPairsRem);
    }


    /**
     * TRUE
     */
    public static TermTransitionPairsSet EMPTY = new TermTransitionPairsSet(Arrays.asList(TermTransitionPair.EMPTY));

    @Override
    public String toString() {
        return this.transPairs.toString();
    }

    public static TermTransitionPairsSet create(final Set<IGeneralizedRule> rules)
    {
        final Set<TermTransitionPair> pairs = new HashSet<>();

        for (final IGeneralizedRule rule : rules) {
            pairs.addAll(TermTransitionPair.create(rule));
        }

        return TermTransitionPairsSet.create(pairs);
    }

    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> variables = new HashSet<>();

        for (final TermTransitionPair tP : this.transPairs) {
            variables.addAll(tP.getVariables());
        }

        return variables;
    }

    public Collection<IGeneralizedRule> createRules(final FunctionSymbol lfSym, final FunctionSymbol rfSym) {
        final Set<IGeneralizedRule> rules = new LinkedHashSet<>();

        for (final TermTransitionPair pair : this.transPairs) {
            rules.add(pair.createRule(lfSym, rfSym));
        }

        return rules;
    }

    public static TermTransitionPairsSet create(final TRSTerm t, final TermRelation rel) {
        final Set<TermTransitionPair> pairs = new HashSet<>();

        try {
            for (final TRSTerm c : TermTools.getDNF(t)) {
                pairs.add(new TermTransitionPair(c, rel));
            }
        } catch (final UnsupportedException e) {
            //
        }

        return TermTransitionPairsSet.create(pairs);
    }

    public LinearTransitionPairsSet flatten(
        final Map<FunctionSymbol, Set<String>> fSymToVars,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp,
        final FreshNameGenerator ng)
    {
        final Set<LinearTransitionPair> pairs = new HashSet<>();

        for (final TermTransitionPair p : this.transPairs) {
            pairs.add(p.flatten(fSymToVars, varsToFApp, ng));
        }

        return LinearTransitionPairsSet.create(pairs);
    }

}
