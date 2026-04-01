package aprove.verification.complexity.CpxWeightedTrsProblem;

import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A TRS rule with an integer weight.
 *
 * @author mnaaf
 *
 */
public class WeightedRule
implements
    Immutable,
    Exportable,
    HasFunctionSymbols,
    HasRootSymbol,
    HasVariables,
    HasTRSTerms,
    HasLHS,
    HasRuleForm
{
    private final Pair<Rule,Integer> data;

    private WeightedRule(Rule rule, Integer weight) {
        this.data = new Pair<>(rule,weight);
    }

    public static WeightedRule create(Rule rule, Integer weight) {
        return new WeightedRule(rule,weight);
    }

    public static WeightedRule create(Rule rule) {
        return new WeightedRule(rule,1);
    }

    public static WeightedRule create(TRSFunctionApplication lhs, TRSTerm rhs, Integer weight) {
        return new WeightedRule(Rule.create(lhs,rhs),weight);
    }

    public WeightedRule renameVariables(Set<TRSVariable> forbidden) {
        Rule renamed = this.data.x.renameVariables(forbidden);
        return new WeightedRule(renamed, this.data.y);
    }

    public Rule getRule() {
        return this.data.x;
    }

    public Integer getWeight() {
        return this.data.y;
    }

    @Override
    public TRSFunctionApplication getLeft() {
        return this.data.x.getLeft();
    }

    @Override
    public TRSTerm getRight() {
        return this.data.x.getRight();
    }

    @Override
    public Set<? extends Variable> getVariables() {
        return this.data.x.getVariables();
    }

    public Set<TRSVariable> getTRSVariables() {
        return this.data.x.getVariables();
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return this.data.x.getRootSymbol();
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        return this.data.x.getFunctionSymbols();
    }

    @Override
    public String export(Export_Util eu) {
        return eu.export(this.data.x) + eu.escape(" [") + eu.export(this.data.y) + eu.escape("]");
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    @Override
    public Set<? extends TRSTerm> getTerms() {
        return this.data.x.getTerms();
    }
}
