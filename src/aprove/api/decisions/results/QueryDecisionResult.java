package aprove.api.decisions.results;

import aprove.api.decisions.*;

public class QueryDecisionResult {

    private final QueryDecision decision;
    private final String query;

    public QueryDecisionResult(QueryDecision decision, String query) {
        this.decision = decision;
        this.query = query;
    }

    public QueryDecision getDecision() {
        return decision;
    }

    public String getQuery() {
        return query;
    }
}
