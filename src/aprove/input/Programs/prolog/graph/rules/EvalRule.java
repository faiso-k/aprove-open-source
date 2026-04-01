package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * EvalStep.<br><br>
 *
 * Created: Dec 1, 2006<br>
 * Last modified: Dec 1, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class EvalRule extends AbstractInferenceRule {

    /**
     * The terms which may not unify in the backtracking case.
     */
    private final Pair<PrologTerm, PrologTerm> clash;

    /**
     * The applied clause.
     */
    private final PrologClause clause;

    /**
     * The ground substitution.
     */
    private final PrologSubstitution groundSubstitution;

    /**
     * Thw whole substitution.
     */
    private final PrologSubstitution substitution;

    /**
     * @param c The terms which may not unify.
     */
    public EvalRule(final Pair<PrologTerm, PrologTerm> c) {
        this(null, null, null, c);
    }

    /**
     * @param c The applied clause.
     * @param sigmaPrime The whole substitution.
     * @param sigmaG The ground substitution.
     */
    public EvalRule(final PrologClause c, final PrologSubstitution sigmaPrime, final PrologSubstitution sigmaG) {
        this(c, sigmaPrime, sigmaG, null);
    }

    /**
     * Standard constructor.
     * @param clau The applied clause.
     * @param sigmaPrime The whole substitution.
     * @param sigmaG The ground substitution.
     * @param clas The terms which may not unify.
     */
    public EvalRule(
        final PrologClause clau,
        final PrologSubstitution sigmaPrime,
        final PrologSubstitution sigmaG,
        final Pair<PrologTerm, PrologTerm> clas)
    {
        this.clause = clau;
        this.substitution = sigmaPrime;
        this.groundSubstitution = sigmaG;
        this.clash = clas;
    }

    /**
     * @return The terms which may not unify.
     */
    public Pair<PrologTerm, PrologTerm> getClash() {
        return this.clash;
    }

    /**
     * @return The ground substitution.
     */
    public PrologSubstitution getGroundSubstitution() {
        return this.groundSubstitution;
    }

    /**
     * @return The whole substitution.
     */
    public PrologSubstitution getSubstitution() {
        return this.substitution;
    }

    @Override
    public String prettyToString() {
        return this.getSubstitution() == null ? "EVAL-BACKTRACK" : "EVAL with clause"
            + "\\n"
            + this.clause.prettyToString()
            + ".\\n"
            + "and substitution"
            + this.getSubstitution().prettyToString();
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.EVAL;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        final StringBuilder res = new StringBuilder();
        final boolean hasClash = this.getClash() == null;
        res.append("    node[auto");
        if (hasClash) {
            res.append(",swap");
        }
        res.append("]\n");
        res.append("      {\\textsc{Eval}}\n");
        res.append("    node[auto");
        if (!hasClash) {
            res.append(",swap");
        }
        res.append("]\n");
        res.append("      {$");
        if (hasClash) {
            res.append(this.getSubstitution().restrict(vars).toLaTeX(kb));
        } else {
            final Pair<PrologTerm, PrologTerm> c = this.getClash();
            res.append(c.x.toLaTeX(kb));
            res.append(" \\nsim ");
            res.append(c.y.toLaTeX(kb));
        }
        res.append("$}\n");
        return res.toString();
    }

    @Override
    public String toString() {
        return this.getSubstitution() == null ? "EVAL-BACKTRACK" : "EVAL with clause"
            + "\n"
            + this.clause.toString()
            + ".\n"
            + "and substitution"
            + this.getSubstitution().toString();
    }

}
