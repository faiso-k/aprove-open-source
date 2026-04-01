package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBounds.*;
import aprove.verification.oldframework.BasicStructures.*;

public class RTEnrichmentBuilder extends EnrichmentBuilder {

    private Set<Rule> PWithoutRuleToRemove;
    private Rule ruleToRemove;

    public RTEnrichmentBuilder(Bound enrichment, Set<Rule> origTRS, Set<Rule> PWithoutRuleToRemove, Rule ruleToRemove) {
        super(enrichment, origTRS);
        assert (this.enrichment == Bound.MATCHRT || this.enrichment == Bound.MATCHRAISERT);

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

    @Override
    protected void updateEnrichedTRS() {
        for (Rule rule : this.origTRS) {
            TRSFunctionApplication lhs = rule.getLeft();
            TRSTerm rhs = rule.getRight();
            Set<Position> match = this.getMatchPositions(rule);
            this.createERTR(lhs, rhs, match);
        }
        for (Rule rule : this.PWithoutRuleToRemove) {
            TRSFunctionApplication lhs = rule.getLeft();
            TRSTerm rhs = rule.getRight();
            Set<Position> match = this.getMatchPositions(rule);
            this.createERTR(lhs, rhs, match);
        }
        TRSFunctionApplication lhs = this.ruleToRemove.getLeft();
        TRSTerm rhs = this.ruleToRemove.getRight();
        Set<Position> match = this.getMatchPositions(this.ruleToRemove);
        this.createER(lhs, rhs, match);
    }
}
