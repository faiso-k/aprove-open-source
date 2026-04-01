package aprove.verification.dpframework.Orders.SizeChangeNP;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.SCNPOrder.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Encoding comparison between two multisets of tagged terms.
 *
 * @author Carsten Fuhs
 */
public interface PRuleEncoder {

    /**
     * Encodes max comparison between the results of the level mapping
     * for rule.
     *
     * @param rule - must have a function application on its rhs
     * @param arcsStrictWeak - the encoded size change arcs for rule
     *  (arcsStrictWeak[i][j] should contain the pair
     *  (|| l_i > r_j ||, || l_i >= r_j ||) if rule has the shape
     *  F(l_1, ..., l_k) -> G(r_1, ..., r_n)
     * @param levelMapping - contains encoding of arg filters,
     *  among other things
     * @param ff - used for constructing the formulae
     * @param strict - true: GR comparison; false: GE comparison
     * @param aborter
     * @return a formula that states l >(=) r for a rule l -> r
     *  (strict == true means >, strict == false means >=)
     * @throws AbortionException
     */
    Formula<None> encodeRule(GeneralizedRule rule,
            Pair<Formula<None>, Formula<None>>[][] arcsStrictWeak,
            LevelMappingEncoder levelMapping, FormulaFactory<None> ff, SATPatterns<None> sp, boolean strict, boolean rootArg,
            Abortion aborter) throws AbortionException;

    /**
     * Encodes max comparison between the results of the level mapping
     * for the rules of p.
     *
     * @param ruleToStrictWeak - the encoded size change arcs for rules
     *  (ruleToStrictWeak.get(rule)[i][j] should contain the pair
     *  (|| l_i > r_j ||, || l_i >= r_j ||) if rule has the shape
     *  F(l_1, ..., l_k) -> G(r_1, ..., r_n)
     * @param levelMapping - will be used to figure out which arguments
     *  are regarded
     * @param ff - used for constructing the formulae
     * @param allstrict - true: orient all elements of p strictly,
     *  false: orient all elements of p weakly and at least one
     *  of them strictly
     * @param aborter
     * @return a formula that states that p should be oriented (according
     *  to allstrict)
     * @throws AbortionException
     */
    Formula<None> encodeP(Map<? extends GeneralizedRule, Pair<Formula<None>, Formula<None>>[][]> ruleToStrictWeak,
            LevelMappingEncoder levelMapping, FormulaFactory<None> ff, SATPatterns<None> sp,
            boolean allstrict, boolean rootArg, Abortion aborter) throws AbortionException;

    /**
     * @return what kind of comparison this encoder corresponds to.
     */
    Comparison getComparisonType();
}
