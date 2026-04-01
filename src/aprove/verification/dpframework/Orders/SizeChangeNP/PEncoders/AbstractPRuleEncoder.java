package aprove.verification.dpframework.Orders.SizeChangeNP.PEncoders;

import java.util.*;
import java.util.Map.Entry;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.SizeChangeNP.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class AbstractPRuleEncoder implements PRuleEncoder {

    @Override
    public Formula<None> encodeP(Map<? extends GeneralizedRule, Pair<Formula<None>, Formula<None>>[][]> ruleToStrictWeak, LevelMappingEncoder levelMapping, FormulaFactory<None> ff, SATPatterns<None> sp, boolean allstrict, boolean rootArg,
            Abortion aborter) throws AbortionException {
        Map<GeneralizedRule,Pair<Formula<None>,Formula<None>>> ruleToStrictWeakRule = new LinkedHashMap<GeneralizedRule,Pair<Formula<None>,Formula<None>>>();
        for (Entry<? extends GeneralizedRule, Pair<Formula<None>, Formula<None>>[][]> ruleArcs : ruleToStrictWeak.entrySet()) {
            GeneralizedRule rule = ruleArcs.getKey();
            Pair<Formula<None>, Formula<None>>[][] arcs = ruleArcs.getValue();
            Formula<None> ruleStrict = this.encodeRule(rule, arcs, levelMapping,
                    ff, sp, true, rootArg, aborter);
            Formula<None> ruleWeak = this.encodeRule(rule, arcs, levelMapping,
                    ff, sp, false, rootArg, aborter);
            ruleToStrictWeakRule.put(rule, new Pair<Formula<None>,Formula<None>>(ruleStrict, ruleWeak));
        }
        List<Formula<None>> strictComparisons = new ArrayList<Formula<None>>(ruleToStrictWeak.size());
        for (Entry<? extends GeneralizedRule, Pair<Formula<None>, Formula<None>>> ruleToRuleStrictWeak : ruleToStrictWeakRule.entrySet()) {
            GeneralizedRule rule = ruleToRuleStrictWeak.getKey();
            Pair<Formula<None>,Formula<None>> ruleStrictWeak = ruleToRuleStrictWeak.getValue();
            Formula<None> ruleStrict = ruleStrictWeak.x;
            Formula<None> currentStrict;
            if (levelMapping.getPlainRoot()) {
                currentStrict = ruleStrict;
            } else {
                //TODO: cache me
                Formula<None> ruleWeak = ruleStrictWeak.y;
                FunctionSymbol lSym = rule.getLeft().getRootSymbol();
                FunctionSymbol rSym = ((TRSFunctionApplication)rule.getRight()).getRootSymbol();
                Formula<None> tagStrict = levelMapping.encodeRootTag(lSym, rSym, true);
                currentStrict = ff.buildOr(ruleStrict, ff.buildAnd(tagStrict, ruleWeak));
            }
            strictComparisons.add(currentStrict);
        }
        Formula<None> result;
        if (allstrict) {
            result = ff.buildAnd(strictComparisons);
        }
        else {
            List<Formula<None>> conjuncts = new ArrayList<Formula<None>>(1+ruleToStrictWeak.size());
            Formula<None> someStrict = ff.buildOr(strictComparisons);
            conjuncts.add(someStrict);
            for (Entry<? extends GeneralizedRule, Pair<Formula<None>, Formula<None>>> ruleToRuleStrictWeak : ruleToStrictWeakRule.entrySet()) {
                GeneralizedRule rule = ruleToRuleStrictWeak.getKey();
                Pair<Formula<None>,Formula<None>> ruleStrictWeak = ruleToRuleStrictWeak.getValue();
                Formula<None> ruleWeak = ruleStrictWeak.y;
                Formula<None> currentWeak;
                if (levelMapping.getPlainRoot()) {
                    currentWeak = ruleWeak;
                } else {
                    Formula<None> ruleStrict = ruleStrictWeak.x;
                    FunctionSymbol lSym = rule.getLeft().getRootSymbol();
                    FunctionSymbol rSym = ((TRSFunctionApplication)rule.getRight()).getRootSymbol();
                    Formula<None> tagWeak = levelMapping.encodeRootTag(lSym, rSym, false);
                    currentWeak = ff.buildOr(ruleStrict, ff.buildAnd(tagWeak, ruleWeak));
                }
                conjuncts.add(currentWeak);
            }
            result = ff.buildAnd(conjuncts);
        }
        return result;
    }

    @Override
    public abstract Formula<None> encodeRule(GeneralizedRule rule,
            Pair<Formula<None>, Formula<None>>[][] arcsStrictWeak,
            LevelMappingEncoder levelMapping, FormulaFactory<None> ff, SATPatterns<None> sp, boolean strict, boolean rootArg,
            Abortion aborter) throws AbortionException;
}
