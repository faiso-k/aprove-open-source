package aprove.verification.dpframework.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import immutables.*;

/**
 * Provides a method to remove conflicts of symbols in a TRS
 * with predefined symbols.
 *
 * @author noschinski
 *
 * TODO: Add work-on-names-instead-of-symbols option?
 *
 */
public class NameConflictResolver {

    private final FreshNameEnsurer freshNames;

    private NameConflictResolver(NameProvider from, NameProvider to, NameGenerator gen) {
        this.freshNames = FreshNameEnsurer.create(from, to, gen);
    }

    /**
     * FIXME
     *
     * <p>
     * Removes conflicts between predefined function symbols when transforming
     * between different kind of TRS or DP problems (e.g. CLS to ITRS).
     * </p>
     *
     * <p>
     * Usage is intended as follows: FIXME
     * </p>
     *
     * @param from
     *            FunctionSymbols which may not be replaced. This can be used to
     *            keep function symbols intact, which need an explicit
     *            conversion to the new problem format (e.g. predefined symbols
     *            in the source problem).
     * @param to
     *            FunctionSymbols which shall be replaced. If a FunctionSymbols
     *            is also in ignoreSymbols, its presence in removeSymbols is
     *            ignored.
     * @param gen
     *            NameGenerator used to generate fresh names.
     */
    public static NameConflictResolver create(
            NameProvider from, NameProvider to, NameGenerator gen) {
        return new NameConflictResolver(from, to, gen);
    }

    public static NameConflictResolver create(NameProvider from, NameProvider to) {
        NameGenerator gen = new PrefixNameGenerator("U");
        return new NameConflictResolver(from, to, gen);
    }

    public TRSFunctionApplication transform(TRSFunctionApplication fa) {
        return this.mapTermFreshnames(fa);
    }

    public TRSTerm transform(TRSTerm t) {
        return this.mapTermFreshnames(t);
    }

    public Rule transform(Rule r) {
        TRSFunctionApplication newLhs = this.mapTermFreshnames(r.getLeft());
        TRSTerm newRhs = this.mapTermFreshnames(r.getRight());
        return Rule.create(newLhs, newRhs);
    }

    public Set<Rule> transform(Set<Rule> rs) {
        Set<Rule> newRs = new HashSet<Rule>(rs.size());
        for (Rule r : rs) {
            newRs.add(this.transform(r));
        }
        return newRs;
    }

    public ConditionalRule transformConditional(ConditionalRule r) {
        TRSFunctionApplication newLhs = this.mapTermFreshnames(r.getLeft());
        TRSTerm newRhs = this.mapTermFreshnames(r.getRight());
        List<Condition> newCond = new ArrayList<Condition>(
                r.getConditions().size());
        for (Condition cond : r.getConditions()) {
            TRSTerm newLeft = this.mapTermFreshnames(cond.getLeft());
            TRSTerm newRight = this.mapTermFreshnames(cond.getRight());
            newCond.add(Condition.create(newLeft, newRight, cond.getType()));
        }
        return ConditionalRule.create(
                newLhs, newRhs, ImmutableCreator.create(newCond));
    }

    public Set<ConditionalRule> transformConditional(Set<ConditionalRule> rs) {
        Set<ConditionalRule> newRs = new HashSet<ConditionalRule>(rs.size());
        for (ConditionalRule r : rs) {
            newRs.add(this.transformConditional(r));
        }
        return newRs;
    }

    /**
     * Replaces all symbols in a term by fresh names.
     */
    private TRSTerm mapTermFreshnames(TRSTerm term) {
        if (term.isVariable()) {
            return term;
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication)term;
            FunctionSymbol oldRoot = fa.getRootSymbol();

            FunctionSymbol newRoot;

            String oldName = oldRoot.getName();
            String newName = this.freshNames.getFreshName(oldName);
            if (oldName.equals(newName)) {
                newRoot = oldRoot;
            } else {
                newRoot = FunctionSymbol.create(newName, oldRoot.getArity());
            }

            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(oldRoot.getArity());
            for (TRSTerm a : fa.getArguments()) {
                newArgs.add(this.mapTermFreshnames(a));
            }

            return TRSTerm.createFunctionApplication(newRoot, ImmutableCreator.create(newArgs));
        }
    }

    /**
     * Replaces all symbols in a function application by fresh names.
     */
    private TRSFunctionApplication mapTermFreshnames(TRSFunctionApplication fa) {
        return (TRSFunctionApplication)this.mapTermFreshnames((TRSTerm)fa);
    }


}
