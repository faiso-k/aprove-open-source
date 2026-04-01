package aprove.input.Programs.prolog.graph;

import java.util.*;

import org.json.*;

import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * A goal element.<br><br>
 *
 * Created: Sep 3, 2008<br>
 * Last modified: Aug 19, 2015
 *
 * @author cryingshadow
 * @version $Id$
 */
public class GoalElement implements PrettyStringable, Immutable, JSONExport {

    /**
     * Value for a goal element not being labeled with a clause.
     */
    public static final int NO_CLAUSE = -1;

    /**
     * Value for a goal element not having a scope.
     */
    public static final int NO_SCOPE = -1;

    /**
     * The index of the clause to be applied.
     */
    private final int applicableClause;

    /**
     * The scope index.
     */
    private final int scope;

    /**
     * The term contained in this goal element.
     */
    private final PrologTerm term;

    public GoalElement(int scope) {
        this(null, scope, GoalElement.NO_CLAUSE);
    }

    public GoalElement(PrologTerm t) {
        this(t, GoalElement.NO_SCOPE, GoalElement.NO_CLAUSE);
    }

    public GoalElement(PrologTerm t, int scope, int clause) {
        this.term = t;
        this.scope = scope;
        this.applicableClause = clause;
    }

    public GoalElement applySubstitution(Map<? extends PrologVariable, ? extends PrologTerm> sigma) {
        if (this.isQuestionMark()) {
            return this;
        } else {
            return new GoalElement(
                this.getTerm().applySubstitution(sigma),
                this.getScope(),
                this.getApplicableClause()
            );
        }
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof GoalElement) {
            GoalElement s = (GoalElement) o;
            return
                this.isQuestionMark() ?
                    s.isQuestionMark() && this.scope == s.scope :
                        this.term.equals(s.term)
                        && this.scope == s.scope
                        && this.applicableClause == s.applicableClause;
        }
        return false;
    }

    /**
     * @return the applicableClause
     */
    public int getApplicableClause() {
        return this.applicableClause;
    }

    /**
     * @return the scope
     */
    public int getScope() {
        return this.scope;
    }

    /**
     * @return the term
     */
    public PrologTerm getTerm() {
        return this.term;
    }

    public boolean hasApplicableClause() {
        return this.applicableClause != GoalElement.NO_CLAUSE;
    }

    @Override
    public int hashCode() {
        if (this.isQuestionMark()) {
            return this.scope;
        } else {
            return this.term.hashCode() * 3 + this.scope * 7 + this.applicableClause * 5 + 11;
        }
    }

    /**
     * @return
     */
    public boolean isQuestionMark() {
        return this.term == null;
    }

    @Override
    public String prettyToString() {
        if (this.isQuestionMark()) {
            return "?_" + this.scope;
        } else {
            if (this.hasApplicableClause()) {
                StringBuilder res = new StringBuilder();
                res.append(this.term.prettyToString());
                res.append(", SCOPE: ");
                res.append(this.scope);
                res.append(", CLAUSE: ");
                res.append(this.applicableClause);
                return res.toString();
            } else {
                return this.term.prettyToString();
            }
        }
    }

    public GoalElement replaceTerm(PrologTerm term) {
        return new GoalElement(term, this.getScope(), this.getApplicableClause());
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = new JSONObject();
        res.put("term", JSONExportUtil.toJSON(this.term));
        res.put("clause", this.applicableClause);
        res.put("scope", this.scope);
        return res;
    }

    public String toLaTeX(KnowledgeBase kb) {
        if (this.isQuestionMark()) {
            return "\\, ?_{" + this.getScope() + "}";
        } else {
            StringBuilder res = new StringBuilder();
            if (this.hasApplicableClause()) {
                res.append("(");
            }
            if (this.getTerm().isTrue()) {
                res.append("\\Box");
            } else {
                res.append(this.getTerm().toLaTeX(kb));
            }
            if (this.hasApplicableClause()) {
                res.append(")^{(");
                res.append(this.getApplicableClause());
                res.append(")}");
            }
            return res.toString();
        }
    }

    @Override
    public String toString() {
        if (this.isQuestionMark()) {
            return "?_" + this.scope;
        } else {
            if (this.hasApplicableClause()) {
                StringBuilder res = new StringBuilder();
                res.append(this.term.toString());
                res.append(", SCOPE: ");
                res.append(this.scope);
                res.append(", CLAUSE: ");
                res.append(this.applicableClause);
                return res.toString();
            } else {
                return this.term.toString();
            }
        }
    }

}
