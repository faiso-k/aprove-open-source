package aprove.input.Programs.prolog.graph;

import java.util.*;

import aprove.input.Programs.prolog.structure.*;

/**
 * Holds a triple which represents applicable clauses.
 */
public class RestrictedUnifier {


    /** The MGU for this clause.*/
    private Map<PrologVariable, PrologTerm> mgu;

    /** The clause.*/
    private PrologClause clause;

    /** Equivalence classes of abstract variable w.r.t. unification. */
    private Set<Set<PrologAbstractVariable>> unifyingAbstractVars;

    public RestrictedUnifier(Map<PrologVariable, PrologTerm> mgu, PrologClause clause, Set<Set<PrologAbstractVariable>> unifyingAbstractVars) {
        this.mgu = mgu;
        this.clause = clause;
        this.unifyingAbstractVars = unifyingAbstractVars;
    }

    public PrologClause getClause() {
        return this.clause;
    }

    public Map<PrologVariable, PrologTerm> getMgu() {
        return this.mgu;
    }

    public Set<Set<PrologAbstractVariable>> getUnifyingAbstractVars() {
        return this.unifyingAbstractVars;
    }

}

