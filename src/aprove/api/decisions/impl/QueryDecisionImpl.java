package aprove.api.decisions.impl;

import java.util.*;

import aprove.api.decisions.*;
import aprove.api.decisions.results.*;

public class QueryDecisionImpl implements QueryDecision {

    public QueryDecisionResult makeDecision(String query) throws InvalidDecisionException {
        Objects.requireNonNull(query);
        if (!query.isEmpty()) {
            return new QueryDecisionResult(this, query);
        } else {
            throw new InvalidDecisionException("the query cannot be empty");
        }
    }
}
