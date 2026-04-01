package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBounds.*;
import aprove.verification.oldframework.BasicStructures.*;

public class DPEnrichmentBuilder extends EnrichmentBuilder {

    private Set<Rule> PWithoutRuleToRemove;
    private Rule ruleToRemove;

    public DPEnrichmentBuilder(Bound enrichment, Set<Rule> origTRS, Set<Rule> PWithoutRuleToRemove, Rule ruleToRemove) {
        super(enrichment, origTRS);
        assert (this.enrichment == Bound.TOPDP || this.enrichment == Bound.TOPRAISEDP || this.enrichment == Bound.MATCHDP || this.enrichment == Bound.MATCHRAISEDP);

        this.PWithoutRuleToRemove = PWithoutRuleToRemove;
        this.ruleToRemove = ruleToRemove;

        for (Rule r : origTRS) {
            for (FunctionSymbol f : r.getLeft().getFunctionSymbols()) {
                this.annotLhsSignature.add(this.lift(f, 0));
            }
        }
        for (Rule r : PWithoutRuleToRemove) {
            for (FunctionSymbol f : r.getLeft().getFunctionSymbols()) {
                this.annotLhsSignature.add(this.lift(f, 0));
            }
        }
        for (FunctionSymbol f : ruleToRemove.getLeft().getFunctionSymbols()) {
            this.annotLhsSignature.add(this.lift(f, 0));
        }

        this.updateEnrichedTRS();
    }

    public Rule getRuleToRemove() {
        return this.ruleToRemove;
    }

    public Set<Rule> getPWithoutRuleToRemove() {
        return this.PWithoutRuleToRemove;
    }

    @Override
    protected void updateEnrichedTRS() {
        if (this.enrichment == Bound.TOPDP || this.enrichment == Bound.TOPRAISEDP) {
            for (Rule rule : this.origTRS) {
                TRSFunctionApplication lhs = rule.getLeft();
                TRSTerm rhs = rule.getRight();
                Set<Position> top = this.getTopPositions(rule);
                this.createEDPR(lhs, rhs, top);
            }
            for (Rule rule : this.PWithoutRuleToRemove) {
                TRSFunctionApplication lhs = rule.getLeft();
                TRSTerm rhs = rule.getRight();
                Set<Position> top = this.getTopPositions(rule);
                this.createEDPR(lhs, rhs, top);
            }
            TRSFunctionApplication lhs = this.ruleToRemove.getLeft();
            TRSTerm rhs = this.ruleToRemove.getRight();
            this.getRoofPositions(this.ruleToRemove);
            Set<Position> top = this.getTopPositions(this.ruleToRemove);
            this.createER(lhs, rhs, top);

        } else if (this.enrichment == Bound.MATCHDP || this.enrichment == Bound.MATCHRAISEDP) {
            for (Rule rule : this.origTRS) {
                TRSFunctionApplication lhs = rule.getLeft();
                TRSTerm rhs = rule.getRight();
                Set<Position> match = this.getMatchPositions(rule);
                this.createEDPR(lhs, rhs, match);
            }
            for (Rule rule : this.PWithoutRuleToRemove) {
                TRSFunctionApplication lhs = rule.getLeft();
                TRSTerm rhs = rule.getRight();
                Set<Position> match = this.getMatchPositions(rule);
                this.createEDPR(lhs, rhs, match);
            }
            TRSFunctionApplication lhs = this.ruleToRemove.getLeft();
            TRSTerm rhs = this.ruleToRemove.getRight();
            Set<Position> match = this.getMatchPositions(this.ruleToRemove);
            this.createER(lhs, rhs, match);
        }
    }
}
