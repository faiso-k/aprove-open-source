package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBounds.*;
import aprove.verification.oldframework.BasicStructures.*;

public class TRSEnrichmentBuilder extends EnrichmentBuilder {

    public TRSEnrichmentBuilder(Bound enrichment, Set<Rule> origTRS) {
        super(enrichment, origTRS);
        assert (enrichment == Bound.ROOF || enrichment == Bound.ROOFRAISE || enrichment == Bound.MATCH || enrichment == Bound.MATCHRAISE);

        for (Rule r : origTRS) {
            for (FunctionSymbol f : r.getLeft().getFunctionSymbols()) {
                this.annotLhsSignature.add(this.lift(f, 0));
            }
        }

        this.updateEnrichedTRS();
    }

    @Override
    protected void updateEnrichedTRS() {
        if (this.enrichment == Bound.ROOF || this.enrichment == Bound.ROOFRAISE) {
            for (Rule rule : this.origTRS) {
                TRSFunctionApplication lhs = rule.getLeft();
                TRSTerm rhs = rule.getRight();

                Set<Position> roof = this.getRoofPositions(rule);

                this.createER(lhs, rhs, roof);
            }

        } else if (this.enrichment == Bound.MATCH || this.enrichment == Bound.MATCHRAISE) {
            for (Rule rule : this.origTRS) {
                TRSFunctionApplication lhs = rule.getLeft();
                TRSTerm rhs = rule.getRight();

                Set<Position> match = this.getMatchPositions(rule);

                this.createER(lhs, rhs, match);
            }
        }
    }
}
