package aprove.verification.oldframework.IntTRS.PoloRedPair;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Here we split DNF conditions into its clauses
 * and we rename the variable, so that different rules
 * use different variables.
 * Furthermore we remove rules that are equal modulo variable
 * renaming.
 * @author Matthias Hoelzel
 */
public class RulePreparation {
    /** A name generator */
    private final FreshNameGenerator ng;

    /**
     * It is a constructor!
     * @param gen name generator
     */
    public RulePreparation(final FreshNameGenerator gen) {
        this.ng = gen;
    }

    /**
     * Prepares the given problem.
     * @param input some integer rewrite system
     * @return another integer rewrite system
     */
    public IRSProblem preprareIntTRSProblem(final IRSProblem input) {
        final Set<IGeneralizedRule> preparedRules = this.prepare(input.getRules());
        return new IRSProblem(ImmutableCreator.create(preparedRules), input.getStartTerm());
    }

    /**
     * Prepare the rules.
     * @param kittelRules an int-TRS
     * @return set of rules
     */
    public Set<IGeneralizedRule> prepare(final Set<IGeneralizedRule> kittelRules) {
        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("preparation");
            l.logln("Rules:");
            for (final IGeneralizedRule iRule : kittelRules) {
                l.logln(iRule.toString());
            }
            l.logln();
        }

        final Set<IGeneralizedRule> result = new LinkedHashSet<IGeneralizedRule>(kittelRules.size());

        for (final IGeneralizedRule iRule : kittelRules) {
            TRSTerm condition = iRule.getCondTerm();
            condition = condition != null ? condition : ToolBox.PREDEFINED.getBooleanTrue().getTerm();
            final List<TRSTerm> clauses = this.getDNFClauses(condition);
            for (final TRSTerm clause : clauses) {
                final IGeneralizedRule newRule = IGeneralizedRule.create(iRule.getLeft(), iRule.getRight(), clause);
                result.add(newRule);
            }
        }

        return result;
    }

    /**
     * Return the disjunction clauses of a DNF-condition term.
     * @param dnfCondition a term in DNF
     * @return list of condition terms
     */
    private List<TRSTerm> getDNFClauses(final TRSTerm dnfCondition) {
        final List<TRSTerm> result = new LinkedList<TRSTerm>();
        this.findDNFClauses(dnfCondition, result);
        return result;
    }

    /**
     * Finds DNF-clauses and adds them.
     * @param dnfCondition condition to investigate
     * @param toInsert list to insert clauses
     */
    private void findDNFClauses(final TRSTerm dnfCondition, final List<TRSTerm> toInsert) {
        if (dnfCondition.isVariable()) {
            assert false : "Condition is variable?!";
            return;
        }
        final TRSFunctionApplication funDnfCondition = (TRSFunctionApplication) dnfCondition;
        final FunctionSymbol sym = funDnfCondition.getRootSymbol();
        if (ToolBox.PREDEFINED.isLor(sym)) {
            for (final TRSTerm arg : funDnfCondition.getArguments()) {
                this.findDNFClauses(arg, toInsert);
            }
        } else {
            toInsert.add(dnfCondition);
        }
    }
}
