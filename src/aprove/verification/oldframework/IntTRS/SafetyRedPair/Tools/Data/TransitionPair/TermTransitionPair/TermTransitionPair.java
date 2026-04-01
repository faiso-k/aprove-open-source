package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.TermTransitionPair;

import java.util.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.LinearRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation.TermRelation.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Pair of a Term without disjunction and negations as the condition and a a TermRelation
 * @author marinag
 */
public class TermTransitionPair extends ImmutablePair<TRSTerm, TermRelation> {

    /**
     * @param condition given condition without disjunction and negations
     * @param TermRelation TermRelation
     */
    public TermTransitionPair(final TRSTerm condition, final TermRelation TermRelation) {
        super(condition, TermRelation);
    }

    /**
     * @return true if the disjunction is empty (=FALSE)
     */
    public boolean isEmpty() {
        return TermTools.PREDEFINED.getBooleanFalse().equals(this.x);
    }

    /**
     * Empty transition pair (=TRUE)
     */
    public static TermTransitionPair EMPTY = new TermTransitionPair(TermTools.TRUE, TermRelation.create());

    public static Set<TermTransitionPair> create(
        final IGeneralizedRule rule)
        {
        final FunctionSymbol fromSym = rule.getLeft().getRootSymbol();
        final FunctionSymbol toSym = ((TRSFunctionApplication) rule.getRight()).getRootSymbol();

        TRSTerm condition = rule.getCondTerm() == null ? TermTools.TRUE : rule.getCondTerm();

        IGeneralizedRule ruleNorm = IGeneralizedRule.create(rule.getLeft(), rule.getRight(), condition);

        ruleNorm = TermTransitionPair.normalize(ruleNorm);

        condition = ruleNorm.getCondTerm();

        final List<Pair<TRSVariable, TRSTerm>> rel = new ArrayList<>();

        for (int i = 0; i < fromSym.getArity(); i++) {
            rel.add(new Pair<>(
                (TRSVariable) ruleNorm.getLeft().getArgument(i),
                ((TRSFunctionApplication) ruleNorm.getRight())
                .getArgument(i)));
        }

        final TermRelation relation = TermRelation.createRelation(rel);
        final Set<TermTransitionPair> result = new HashSet<>();

        try {
            for (final TRSTerm c : TermTools.getDNF(condition)) {
                if (TermTools.isFalse(c)) {
                    continue;
                }

                result.add(new TermTransitionPair(c, relation));
            }
        } catch (final UnsupportedException e) {
            result.add(new TermTransitionPair(TermTools.TRUE, relation));
        }
        return result;
        }

    /**
     * @param rule
     * @return
     */
    private static IGeneralizedRule normalize(final IGeneralizedRule rule) {
        final Map<TRSVariable, TRSVariable> replaceMap = new HashMap<>();
        int id = 0;

        final ArrayList<TRSTerm> args = new ArrayList<>();

        for (final TRSTerm v : rule.getLeft().getArguments()) {
            final TRSVariable var = TRSTerm.createVariable("y" + String.valueOf(id++));
            replaceMap.put((TRSVariable) v, var);
            args.add(var);
        }

        assert (replaceMap.keySet().size() == replaceMap.values().size());

        final TRSSubstitution subst = TRSSubstitution.create(ImmutableCreator.create(replaceMap));

        return IGeneralizedRule.create(
            rule.getLeft().applySubstitution(subst),
            rule.getRight().applySubstitution(subst),
            (rule.getCondTerm() == null ? ToolBox.buildTrue() : rule
                .getCondTerm()
                .applySubstitution(subst)));
    }

    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> variables = new HashSet<>();

        for (final Pair<String, TRSTerm> entry : this.y.getTransitions()) {
            variables.add(TRSTerm.createVariable(entry.getKey()));
            variables.addAll(entry.getValue().getVariables());
        }

        return variables;
    }

    public IGeneralizedRule createRule(final FunctionSymbol lfSym, final FunctionSymbol rfSym) {
        final ArrayList<TRSTerm> argl = new ArrayList<>(lfSym.getArity());
        final ArrayList<TRSTerm> argr = new ArrayList<>(rfSym.getArity());


        for (final Pair<String, TRSTerm> pair : this.y.getTransitions()) {
            argl.add(TRSTerm.createVariable(pair.x));
            argr.add(pair.y);
        }

        final TRSFunctionApplication l = TRSTerm.createFunctionApplication(lfSym, argl);
        final TRSTerm r = TRSTerm.createFunctionApplication(rfSym, argr);

        return IGeneralizedRule.create(l, r, this.x);
    }

    public LinearTransitionPair flatten(
        final Map<FunctionSymbol, Set<String>> fSymToVars,
        final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp,
        final FreshNameGenerator ng)
    {
        final LinearConstraintsSystem c = TermTools.flattenConstraintsSystem(this.x, fSymToVars, varsToFApp, ng);
        final PolyRelation r = this.y.flatten(fSymToVars, varsToFApp, ng);

        return new LinearTransitionPair(c, r);
    }

    public static TermTransitionPair compose(final List<TermTransitionPair> pairs) {
        TRSTerm c = TermTools.TRUE;
        TermRelation r = TermRelation.create();

        for (final TermTransitionPair entry : pairs) {
            c = TermTools.buildAnd(c, r.apply(entry.x));
            r = r.compose(entry.y);
        }

        return new TermTransitionPair(c, r);
    }
}
