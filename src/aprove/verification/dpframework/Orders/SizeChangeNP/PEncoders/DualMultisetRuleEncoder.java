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
 * @author Peter Schneider-Kamp
 */
public class DualMultisetRuleEncoder extends AbstractPRuleEncoder implements PRuleEncoder {

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
        if (rArity == 0 && (strict || lArity > 0)) {
            return ff.buildConstant(false);
        }

        List<Formula<None>> lRegards = levelMapping.getRegardedList(lRootSym);
        List<Formula<None>> rRegards = levelMapping.getRegardedList(rRootSym);

        // for all regarded args i of lhs, i.e., conj. over i:
        List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(1+lArity);

        Formula<None>[][] gamma = new Formula[rArity][lArity];
        Formula<None>[][] notGamma = new Formula[rArity][lArity];
        Formula<None>[][] transGamma = new Formula[lArity][rArity];
        Formula<None>[] epsilon = new Formula[rArity];
        Formula<None>[] notEpsilon = new Formula[rArity];

        /* efficiency is not all ... readability means rather have two nested loops
        for (int i = 0; i < lArity; i++) {
            epsilon[i] = ff.buildVariable();
            notEpsilon[i] = ff.buildNot(epsilon[i]);
            for (int j = 0; j < rArity; j++) {
                gamma[i][j] = ff.buildVariable();
                notGamma[i][j] = ff.buildNot(gamma[i][j]);
                List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(3);
                disjuncts.add(notGamma[i][j]);
                disjuncts.add(ff.buildAnd(epsilon[i],arcsStrictWeak[i][j].y));
                disjuncts.add(ff.buildAnd(notEpsilon[i],arcsStrictWeak[i][j].x));
                conjuncts.add(ff.buildOr(disjuncts));
            }
        }*/
        // initialize variables for multiset cover encoding
        for (int j = 0; j < rArity; j++) {
            epsilon[j] = ff.buildVariable();
            notEpsilon[j] = ff.buildNot(epsilon[j]);
            for (int i = 0; i < lArity; i++) {
                gamma[j][i] = ff.buildVariable();
                notGamma[j][i] = ff.buildNot(gamma[j][i]);
                transGamma[i][j] = gamma[j][i];
            }
        }
        // encode that if gamam and epsilon represent a multiset encoding,
        // the correspondig arcs exist
        for (int j = 0; j < rArity; j++) {
            for (int i = 0; i < lArity; i++) {
                List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(3);
                disjuncts.add(notGamma[j][i]);
                disjuncts.add(ff.buildAnd(epsilon[j],arcsStrictWeak[i][j].y));
                disjuncts.add(ff.buildAnd(notEpsilon[j],arcsStrictWeak[i][j].x));
                conjuncts.add(ff.buildOr(disjuncts));
            }
        }

        // in the strict case there must be some argument that is not used for equality
        if (strict) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(rArity);
            for (int j = 0; j < rArity; j++) {
                disjuncts.add(ff.buildAnd(rRegards.get(j),notEpsilon[j]));
            }
            conjuncts.add(ff.buildOr(disjuncts));
        }

        // if some argument of lhs is regarded, it must be covered
        for (int i = 0; i < lArity; i++) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(2);
            disjuncts.add(ff.buildNot(lRegards.get(i)));
            disjuncts.add(sp.encodeExactlyOne(transGamma[i]));
            conjuncts.add(ff.buildOr(disjuncts));
        }
        // if some argument of lhs is not regarded, it cannot be covered
        for (int i = 0; i < lArity; i++) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(2);
            disjuncts.add(lRegards.get(i));
            disjuncts.add(sp.encodeNone(transGamma[i]));
            conjuncts.add(ff.buildOr(disjuncts));
        }
        // if some argument of rhs is not regarded, it cannot cover something
        for (int j = 0; j < rArity; j++) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(2);
            disjuncts.add(rRegards.get(j));
            disjuncts.add(sp.encodeNone(gamma[j]));
            conjuncts.add(ff.buildOr(disjuncts));
        }
        // if some argument of rhs is used for equality, it covers exactly one thing
        for (int j = 0; j < rArity; j++) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(2);
            disjuncts.add(notEpsilon[j]);
            disjuncts.add(sp.encodeExactlyOne(gamma[j]));
            conjuncts.add(ff.buildOr(disjuncts));
        }

        Formula<None> result = ff.buildAnd(conjuncts);
        return result;
    }

    @Override
    public Comparison getComparisonType() {
        return Comparison.DMS;
    }

}
