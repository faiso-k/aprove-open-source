package aprove.verification.dpframework.Orders.SizeChangeNP.PEncoders;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.SCNPOrder.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Max comparison of multisets/lists:
 * [s_1, ..., s_k] >(=) [t_1, ..., t_n]
 *   iff
 * for all t_j there exists s_i with s_i >(=) t_j
 *
 * For >, we moreover require that k >= 1
 * (i.e., the left list must not be empty).
 *
 * @author Carsten Fuhs
 */
public class MaxRuleEncoder extends AbstractPRuleEncoder implements PRuleEncoder {

    @Override
    public Formula<None> encodeRule(GeneralizedRule rule,
            Pair<Formula<None>, Formula<None>>[][] arcsStrictWeak,
            LevelMappingEncoder levelMapping,
            FormulaFactory<None> ff, SATPatterns<None> sp, boolean strict, boolean rootArg, Abortion aborter)
                throws AbortionException {
        FunctionSymbol lRootSym = rule.getLeft().getRootSymbol();
        final int lArity = lRootSym.getArity() + (rootArg ? 1 : 0);
        FunctionSymbol rRootSym = ((TRSFunctionApplication)rule.getRight()).getRootSymbol();
        final int rArity = rRootSym.getArity() + (rootArg ? 1 : 0);
        if (lArity == 0 && (strict || rArity > 0)) {
            return ff.buildConstant(false);
        }

        List<Formula<None>> lRegards = levelMapping.getRegardedList(lRootSym);
        List<Formula<None>> rRegards = levelMapping.getRegardedList(rRootSym);

        // for all regarded args j of rhs, i.e., conj. over j:
        List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(1+rArity);

        // (first of all, make sure that for strict comparison some lhs arg
        // is actually regarded if we orient strictly)
        if (strict) {
            conjuncts.add(ff.buildOr(lRegards));
        }

        for (int j = 0; j < rArity; ++j) {
            // there is a regarded arg i on the lhs with an arc
            // such that l_i >(=) r_j, i.e.,
            // regarded_j -> disj. over i: regarded_i and arc_from_i_to_j
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(lArity+1);
            Formula<None> rRegardsJ = rRegards.get(j);
            disjuncts.add(ff.buildNot(rRegardsJ));
            for (int i = 0; i < lArity; ++i) {
                Formula<None> lRegardsI = lRegards.get(i);
                Pair<Formula<None>, Formula<None>> arcsIJ = arcsStrictWeak[i][j];
                Formula<None> liCompRj = strict ? arcsIJ.x : arcsIJ.y;
                disjuncts.add(ff.buildAnd(lRegardsI, liCompRj));
            }
            conjuncts.add(ff.buildOr(disjuncts));
            aborter.checkAbortion();
        }
        Formula<None> result = ff.buildAnd(conjuncts);
        return result;
    }

    @Override
    public Comparison getComparisonType() {
        return Comparison.MAX;
    }

}
