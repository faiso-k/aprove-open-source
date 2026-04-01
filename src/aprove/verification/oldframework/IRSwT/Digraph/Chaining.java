package aprove.verification.oldframework.IRSwT.Digraph;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.TerminationGraph.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Chains two given (variable disjoint) rules
 * l1 -> r1 | phi1 (R1)
 * l2 -> r2 | phi2 (R2)
 * into
 * l1 sigma -> r2 sigma | phi1 land phi2 sigma where
 * sigma is the unifier of r1 and l2.
 * It might happen, that sigma does not exist or that l1 sigma or r2 sigma
 * are invalid (due to mixed sorts).
 * In these cases R2 cannot be used after R1, so we return null instead.
 * Please note that this chaining differs from the "intTRS"-chaining, because we have to deal with terms.
 *
 * @author Matthias Hoelzel
 *
 */
public class Chaining {
    /** First input rule! */
    private final IGeneralizedRule rule1;

    /** Second input rule! */
    private final IGeneralizedRule rule2;

    /** Generates fresh names! */
    private final FreshNameGenerator fng;

    /** Aborter. */
    private final Abortion aborter;

    /**
     * Prepare the chaining. Please note, that this only works,
     * iff the rules are variable disjoint!
     *
     * @param r1 first rule
     * @param r2 second rule
     * @param gen some fresh name generator
     * @param abortion some aborter
     */
    public Chaining(
        final IGeneralizedRule r1,
        final IGeneralizedRule r2,
        final FreshNameGenerator gen,
        final Abortion abortion)
    {
        this.rule1 = ToolBox.moveConstantsToCondition(ToolBox.renameVariablesInRule(r1, gen), gen);
        this.rule2 = ToolBox.moveConstantsToCondition(ToolBox.renameVariablesInRule(r2, gen), gen);
        this.fng = gen;
        this.aborter = abortion;

        final LinkedHashSet<TRSVariable> vars1 = new LinkedHashSet<>(this.rule1.getVariables());
        vars1.addAll(this.rule1.getCondVariables());
        final LinkedHashSet<TRSVariable> vars2 = new LinkedHashSet<>(this.rule2.getVariables());
        vars2.addAll(this.rule2.getCondVariables());

        for (final TRSVariable v : vars1) {
            assert !vars2.contains(v) : "Input rules are not variable disjoint:\n" + this.rule1 + "\n" + this.rule2;
        }
        for (final TRSVariable v : vars2) {
            assert !vars1.contains(v) : "Input rules are not variable disjoint:\n" + this.rule1 + "\n" + this.rule2;
        }
    }

    /**
     * Applies the chaining.
     * @return another rule
     * @throws AbortionException can be aborted
     */
    public IGeneralizedRule applyChaining() throws AbortionException {
        final TRSFunctionApplication l1 = this.rule1.getLeft();
        final TRSTerm r1 = this.rule1.getRight();
        final TRSFunctionApplication l2 = this.rule2.getLeft();
        final TRSTerm r2 = this.rule2.getRight();
        TRSTerm phi1 = this.rule1.getCondTerm();
        phi1 = phi1 == null ? ToolBox.buildTrue() : phi1;
        TRSTerm phi2 = this.rule2.getCondTerm();
        phi2 = phi2 == null ? ToolBox.buildTrue() : phi2;

        final TRSSubstitution sigma = r1.getMGU(l2);
        this.aborter.checkAbortion();
        if (sigma != null) {
            final TRSFunctionApplication newLeft = l1.applySubstitution(sigma);
            final TRSTerm newRight = r2.applySubstitution(sigma);
            final TRSTerm newPhi = ToolBox.buildAnd(phi1.applySubstitution(sigma), phi2.applySubstitution(sigma));
            if (Chaining.correctlyTyped(newLeft)
                && Chaining.correctlyTyped(newRight)
                && Chaining.correctlyTyped(newPhi))
            {
                final IGeneralizedRule resultRule = IGeneralizedRule.create(newLeft, newRight, newPhi);
                final RuleSimplification rs = new RuleSimplification(resultRule, this.fng, this.aborter);
                final IGeneralizedRule simplified = rs.simplify();
                return simplified;
            }
        }
        return null;
    }

    /**
     * A term is correctly typed, iff below predefined symbol
     * no non-predefined symbols occur.
     * @param t term to be checked
     * @return boolean
     */
    private static boolean correctlyTyped(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                for (final TRSTerm arg : func.getArguments()) {
                    if (!Chaining.onlyPredefined(arg)) {
                        return false;
                    }
                }
            } else {
                for (final TRSTerm arg : func.getArguments()) {
                    if (!Chaining.correctlyTyped(arg)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * Checks whether or not t only consists of predefined symbols (or variables).
     * @param t term to be checked
     * @return boolean
     */
    private static boolean onlyPredefined(final TRSTerm t) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                return false;
            }
            for (final TRSTerm arg : func.getArguments()) {
                if (!Chaining.onlyPredefined(arg)) {
                    return false;
                }
            }
        }
        return true;
    }
}
