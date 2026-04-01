package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * UnifySuccessRule.<br><br>
 *
 * Created: May 4, 2010<br>
 * Last modified: May 4, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
public class UnifySuccessRule extends AbstractInferenceRule {

    /**
     * The applied substitution.
     */
    private final PrologSubstitution substitution;

    /**
     * The substitution restricted to ground variables.
     */
    private final PrologSubstitution groundSubstitution;

    /**
     * Standard constructor.
     * @param sigmaPrime The whole substitution.
     * @param sigmaG The substitution restricted to ground terms.
     */
    public UnifySuccessRule(final PrologSubstitution sigmaPrime, final PrologSubstitution sigmaG) {
        this.substitution = sigmaPrime;
        this.groundSubstitution = sigmaG;
    }

    /**
     * @return The ground substitution.
     */
    public PrologSubstitution getGroundSubstitution() {
        return this.groundSubstitution;
    }

    /**
     * @return The substitution.
     */
    public PrologSubstitution getSubstitution() {
        return this.substitution;
    }

    @Override
    public String prettyToString() {
        return "UNIFY SUCCESS with substitution" + this.getSubstitution().prettyToString();
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.UNIFY_SUCCESS;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        final StringBuilder res = new StringBuilder();
        res.append("    node[auto]\n");
        res.append("      {\\textsc{UnifySuccess}}\n");
        res.append("    node[auto,swap]\n");
        res.append("      {$");
        res.append(this.getSubstitution().restrict(vars).toLaTeX(kb));
        res.append("$}\n");
        return res.toString();
    }

    @Override
    public String toString() {
        return "UNIFY SUCCESS with substitution" + this.getSubstitution().toString();
    }

}
