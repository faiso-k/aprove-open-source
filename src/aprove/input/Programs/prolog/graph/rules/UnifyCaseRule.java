package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * UnifyCaseRule.<br><br>
 *
 * Created: May 4, 2010<br>
 * Last modified: May 4, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
public class UnifyCaseRule extends AbstractInferenceRule {

    /**
     * The terms which may not unify in the backtrack case.
     */
    private final Pair<PrologTerm, PrologTerm> clash;

    /**
     * The ground substitution.
     */
    private final PrologSubstitution groundSubstitution;

    /**
     * The whole substitution.
     */
    private final PrologSubstitution substitution;

    /**
     * @param c The terms which may not unify.
     */
    public UnifyCaseRule(Pair<PrologTerm, PrologTerm> c) {
        this(null, null, c);
    }

    /**
     * @param sigmaPrime The whole substitution.
     * @param sigmaG The ground substitution.
     */
    public UnifyCaseRule(PrologSubstitution sigmaPrime, PrologSubstitution sigmaG) {
        this(sigmaPrime, sigmaG, null);
    }

    /**
     * Standard constructor.
     * @param sigmaPrime The whole substitution.
     * @param sigmaG The ground substitution.
     * @param c The terms which may not unify.
     */
    public UnifyCaseRule(
        PrologSubstitution sigmaPrime,
        PrologSubstitution sigmaG,
        Pair<PrologTerm, PrologTerm> c)
    {
        this.substitution = sigmaPrime;
        this.groundSubstitution = sigmaG;
        this.clash = c;
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
        return this.getSubstitution() == null ? "UNIFY-BACKTRACK" : "UNIFY CASE with substitution"
            + this.getSubstitution().prettyToString();
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.UNIFY_CASE;
    }

    @Override
    public String toLaTeX(Set<PrologVariable> vars, KnowledgeBase kb) {
        StringBuilder res = new StringBuilder();
        boolean hasClash = this.getClash() == null;
        res.append("    node[auto");
        if (hasClash) {
            res.append(",swap");
        }
        res.append("]\n");
        res.append("      {\\textsc{UnifyCase}}\n");
        res.append("    node[auto");
        if (!hasClash) {
            res.append(",swap");
        }
        res.append("]\n");
        res.append("      {$");
        if (hasClash) {
            res.append(this.getSubstitution().restrict(vars).toLaTeX(kb));
        } else {
            Pair<PrologTerm, PrologTerm> c = this.getClash();
            res.append(c.x.toLaTeX(kb));
            res.append(" \\nsim ");
            res.append(c.y.toLaTeX(kb));
        }
        res.append("$}\n");
        return res.toString();
    }

    @Override
    public String toString() {
        return this.getSubstitution() == null ? "UNIFY-BACKTRACK" : "UNIFY CASE with substitution"
            + this.getSubstitution().toString();
    }

}
