/*
 * Created on 30.10.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A conditional rule consists of a general rule
 * where the lhs may not be a variable
 * and a set of conditions
 *
 * @author matraf
 */
public final class ConditionalRule
    implements
        Immutable,
        Exportable,
        HasFunctionSymbols,
        HasRootSymbol,
        HasVariables,
        HasTRSTerms,
        CPFAdditional
{

    /*
     * real values
     */
    private final GeneralizedRule rule;
    private final ImmutableList<Condition> conditions;


    protected int hashCode;

    private static boolean checkProperLandR(final TRSFunctionApplication l, final TRSTerm r) {
        return l != null
        && r != null
        ;
    }


    /**
     * creates a new conditional rule.
     *
     * @param rule - a pair l -> r where l is a function application
     * @param conditions a list of conditions
     */
    private ConditionalRule(final GeneralizedRule rule, final ImmutableList<Condition> conditions) {
        if (Globals.useAssertions) {
            assert(ConditionalRule.checkProperLandR(rule.l, rule.r));
            assert(conditions != null);
        }
        this.rule = rule;
        this.conditions = conditions;

        int n=0;
        this.hashCode = rule.hashCode();
        for(final Condition condition : conditions) {
            this.hashCode += condition.hashCode()*((2<<(n++))-1);
        }

    }


    /**
     * creates a new conditional rule l -> r <= c
     * @param l
     * @param r
     * @param c
     */
    public static ConditionalRule create(final TRSFunctionApplication l, final TRSTerm r, final ImmutableList<Condition> c) {
        return new ConditionalRule(GeneralizedRule.create(l, r), c);
    }

    /**
     * creates a new conditional rule rule <= c
     * @param rule
     * @param c
     */
    public static ConditionalRule create(final GeneralizedRule rule, final ImmutableList<Condition> c) {
        return new ConditionalRule(rule, c);
    }

    public static ConditionalRule create(TRSFunctionApplication lhs, TRSTerm rhs) {
        return ConditionalRule.create(lhs, rhs, ImmutableCreator.create(java.util.Collections.<Condition>emptyList()));
    }

    public static ConditionalRule create(Rule r) {
        return ConditionalRule.create(r.getLeft(), r.getRight());
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    /**
     * returns whether two generalized rules are equal
     */
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof ConditionalRule) {
            final ConditionalRule rule = (ConditionalRule) other;
            return this.hashCode == rule.hashCode && this.rule.equals(rule.rule) && this.conditions.equals(rule.conditions);
        }
        return false;
    }

    /**
     * returns the lhs
     */
    public TRSFunctionApplication getLeft() {
        return this.rule.getLeft();
    }

    /**
     * returns the rhs.
     */
    public TRSTerm getRight() {
        return this.rule.getRight();
    }

    /**
     * returns the root symbol of this rule
     * i.e. the root symbol of the lhs
     */
    @Override
    public FunctionSymbol getRootSymbol() {
           return this.rule.l.getRootSymbol();
    }

    /**
     * returns the set of terms occurring in this rule l -> r <= s_1=t_1, ..., s_k=t_k,
     * i.e. {l,r} union {s_i, t_i | 1 <= i <= k}
     */
    @Override
    public Set<TRSTerm> getTerms() {
        final Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        res.add(this.rule.l);
        res.add(this.rule.r);
        for (final Condition cond : this.conditions) {
            res.addAll(cond.getTerms());
        }
        return res;
    }

    /**
     * returns the set of variables occurring in this rule
     */
    @Override
    public ImmutableSet<TRSVariable> getVariables() {
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>(this.rule.l.getVariables());
        vars.addAll(this.rule.r.getVariables());
        for (final Condition cond : this.conditions) {
            vars.addAll(cond.getVariables());
        }
        return ImmutableCreator.create(vars);
    }

    /**
     * returns the set of functionSymbols occurring in this rule
     */
    @Override
    public ImmutableSet<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>(this.rule.l.getFunctionSymbols());
        fs.addAll(this.rule.r.getFunctionSymbols());
        for(final Condition cond : this.conditions) {
            fs.addAll(cond.getFunctionSymbols());
        }
        return ImmutableCreator.create(fs);
    }


    /**
     * checks whether the variable condition for rules in CTRSs holds
     * i.e. whether V(r) \subseteq V(l) \cup V(c) => 3CTRS
     *      and V(s_i) \subseteq V(l) \cup \bigcup_{j=1}^{i-1} V(t_j) => deterministic 3CTRS
     *      when this conditional rule has the form c | l -> r with c = s_i = t_i where 1 <= i <= k
     */
    public boolean isDeterministic3CTRS() {
        final Set<TRSVariable> valid = this.getLeft().getVariables();
        for(final Condition cond : this.conditions) {
            if (!valid.containsAll(cond.getLeft().getVariables())) {
                return false;
            }
            valid.addAll(cond.getRight().getVariables());
        }
        return valid.containsAll(this.getRight().getVariables());
    }

    /**
     * checks whether the variable condition for rules in CTRSs holds
     * @param condRules a set of conditional rules
     * @return true iff all rules are deterministic
     */
    public static boolean isDeterministic3CTRS(final Set<ConditionalRule> condRules) {
        for(final ConditionalRule condRule : condRules) {
            if (!condRule.isDeterministic3CTRS()) {
                return false;
            }
        }
        return true;
    }


    /**
     * checks whether all rhs of conditions are strongly irreducible
     * this check is not complete: there may be strongly irreducible rhs of conditions that are not detected as such
     * <p>
     * It works by looking at every non-variable subterm of a rhs of the conditions and tries to unify it with a lhs of another rule.
     * When this works, the rhs is not strongly irreducible
     * @param rules set of conditional rules with which the strong irreducibility is checked
     * @return true if it could be found out that the rhs of all conditions are strongly irreducible, false otherwise
     */
    public boolean isStronglyIrreducible(final Set<ConditionalRule> rules) {
        for (final Condition cond : this.conditions) {
            final TRSTerm t = cond.getRight();
            final Set<TRSTerm> subterms = new LinkedHashSet<TRSTerm>();
            t.collectSubTerms(subterms,true);
            for (final TRSTerm subterm : subterms) {
                for (final ConditionalRule rule : rules) {
                    final TRSTerm l = rule.getLeft();
                    if (subterm.unifiesVarDisjoint(l)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }


    /**
     * checks whether this is a strongly deterministic 3CTRS rule,
     * i.e. whether it is deterministic and all rhs of conditions
     * are strongly irreducible
     */
    public boolean isStronglyDeterministic3CTRSRule(final Set<ConditionalRule> rules) {
        if (!this.isDeterministic3CTRS()) {
            return false;
        }
        return this.isStronglyIrreducible(rules);
    }


    /**
     * checks whether the passed set of conditional rules are all deterministic 3CTRS rules
.ai     */
    public static boolean isStronglyDeterministic3CTRS(final Set<ConditionalRule> rules) {
        for(final ConditionalRule condRule : rules) {
            if (!condRule.isStronglyDeterministic3CTRSRule(rules)) {
                return false;
            }
        }
        return true;
    }




    @Override
    public String export(final Export_Util eu) {
        final String ruleStr = this.getLeft().export(eu) + " " + eu.rightarrow() + " " + this.getRight().export(eu);
        String condStr = "";
        int remConds = this.conditions.size();
        for(final Condition cond : this.conditions) {
            condStr += cond.export(eu);
            if ((--remConds) > 0) {
                condStr += ", ";
            }
        }

        if (!condStr.equals("")) {
            return ruleStr + eu.escape(" <= ") + condStr;
        }
        return ruleStr;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public ImmutableList<Condition> getConditions() {
        return this.conditions;
    }

    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData, final CPFTag outermostTag) {
        Element lhs = CPFTag.LHS.create(doc, rule.getLeft().toCPF(doc, xmlMetaData));
        Element rhs = CPFTag.RHS.create(doc, rule.getRight().toCPF(doc, xmlMetaData));
        Element cs = CPFTag.CONDITIONS.create(doc);
        for (final Condition c : this.conditions) {
            cs.appendChild(c.toCPF(doc, xmlMetaData));
        }
        return outermostTag.create(doc, lhs, rhs, cs);
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return toCPF(doc, xmlMetaData, CPFTag.RULE);
    }

}
