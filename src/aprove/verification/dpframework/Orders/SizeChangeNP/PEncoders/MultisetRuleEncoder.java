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
public class MultisetRuleEncoder extends AbstractPRuleEncoder implements PRuleEncoder {

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

        Formula<None>[][] gamma = new Formula[lArity][rArity];
        Formula<None>[][] notGamma = new Formula[lArity][rArity];
        Formula<None>[][] transGamma = new Formula[rArity][lArity];
        Formula<None>[] epsilon = new Formula[lArity];
        Formula<None>[] notEpsilon = new Formula[lArity];

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
        for (int i = 0; i < lArity; i++) {
            epsilon[i] = ff.buildVariable();
            notEpsilon[i] = ff.buildNot(epsilon[i]);
            for (int j = 0; j < rArity; j++) {
                gamma[i][j] = ff.buildVariable();
                notGamma[i][j] = ff.buildNot(gamma[i][j]);
                transGamma[j][i] = gamma[i][j];
            }
        }
        // encode that if gamam and epsilon represent a multiset encoding,
        // the correspondig arcs exist
        for (int i = 0; i < lArity; i++) {
            for (int j = 0; j < rArity; j++) {
                List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(3);
                disjuncts.add(notGamma[i][j]);
                disjuncts.add(ff.buildAnd(epsilon[i],arcsStrictWeak[i][j].y));
                disjuncts.add(ff.buildAnd(notEpsilon[i],arcsStrictWeak[i][j].x));
                conjuncts.add(ff.buildOr(disjuncts));
            }
        }

        // in the strict case there must be some argument that is not used for equality
        if (strict) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(lArity);
            for (int i = 0; i < lArity; i++) {
                disjuncts.add(ff.buildAnd(lRegards.get(i),notEpsilon[i]));
            }
            conjuncts.add(ff.buildOr(disjuncts));
        }

        // if some argument of rhs is regarded, it must be covered
        for (int j = 0; j < rArity; j++) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(2);
            disjuncts.add(ff.buildNot(rRegards.get(j)));
            disjuncts.add(sp.encodeExactlyOne(transGamma[j]));
            conjuncts.add(ff.buildOr(disjuncts));
        }
        // if some argument of rhs is not regarded, it cannot be covered
        for (int j = 0; j < rArity; j++) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(2);
            disjuncts.add(rRegards.get(j));
            disjuncts.add(sp.encodeNone(transGamma[j]));
            conjuncts.add(ff.buildOr(disjuncts));
        }
        // if some argument of lhs is not regarded, it cannot cover something
        for (int i = 0; i < lArity; i++) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(2);
            disjuncts.add(lRegards.get(i));
            disjuncts.add(sp.encodeNone(gamma[i]));
            conjuncts.add(ff.buildOr(disjuncts));
        }
        // if some argument of lhs is used for equality, it covers exactly one thing
        for (int i = 0; i < lArity; i++) {
            List<Formula<None>> disjuncts = new ArrayList<Formula<None>>(2);
            disjuncts.add(notEpsilon[i]);
            disjuncts.add(sp.encodeExactlyOne(gamma[i]));
            conjuncts.add(ff.buildOr(disjuncts));
        }

        Formula<None> result = ff.buildAnd(conjuncts);
        return result;
    }

    @Override
    public Comparison getComparisonType() {
        return Comparison.MS;
    }

}
