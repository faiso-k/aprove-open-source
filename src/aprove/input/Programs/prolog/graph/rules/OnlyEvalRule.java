package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * @author cryingshadow
 *
 */
public class OnlyEvalRule extends AbstractInferenceRule {

    /**
     * The applied clause.
     */
    private final PrologClause clause;

    /**
     * The ground substitution.
     */
    private final PrologSubstitution groundSubstitution;

    /**
     * The whole substitution.
     */
    private final PrologSubstitution substitution;

    /**
     * Standard constructor.
     * @param c The applied clause.
     * @param sigmaPrime The whole substitution.
     * @param sigmaG The ground substitution.
     */
    public OnlyEvalRule(final PrologClause c, final PrologSubstitution sigmaPrime, final PrologSubstitution sigmaG) {
        this.clause = c;
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
     * @return The whole substitution.
     */
    public PrologSubstitution getSubstitution() {
        return this.substitution;
    }

    @Override
    public String prettyToString() {
        return "ONLY EVAL with clause"
            + "\\n"
            + this.clause.prettyToString()
            + ".\\n"
            + "and substitution"
            + this.getSubstitution().prettyToString();
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.ONLY_EVAL;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        final StringBuilder res = new StringBuilder();
        res.append("    node[auto]\n");
        res.append("      {\\textsc{OnlyEval}}\n");
        res.append("    node[auto,swap]\n");
        res.append("      {$");
        res.append(this.getSubstitution().restrict(vars).toLaTeX(kb));
        res.append("$}\n");
        return res.toString();
    }

    @Override
    public String toString() {
        return "ONLY EVAL with clause"
            + "\n"
            + this.clause.toString()
            + ".\n"
            + "and substitution"
            + this.getSubstitution().toString();
    }

}
