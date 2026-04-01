package aprove.input.Programs.prolog.graph;

import aprove.input.Programs.prolog.structure.*;

/**
 * @author cryingshadow
 * Stores all relevant results computed during an attempt to apply the EVAL or ONLYEVAL rule.
 */
public class EvalResults {

    /**
     * Is backtrack case possible?
     */
    private final boolean backtrack;

    /**
     * The target body term.
     */
    private final PrologTerm body;

    /**
     * The target KB.
     */
    private final KnowledgeBase evalBase;

    /**
     * The clause head.
     */
    private final PrologTerm head;

    /**
     * The whole substitution.
     */
    private final PrologSubstitution sigma;

    /**
     * The substitution restricted to ground variables.
     */
    private final PrologSubstitution sigmaG;

    /**
     * The source term.
     */
    private final PrologTerm term;

    /**
     * The applied clause.
     */
    private final PrologClause toApply;

    /**
     * Standard constructor.
     * @param back Is backtrack case possible?
     * @param b The target body term.
     * @param kb The target KB.
     * @param h The clause head.
     * @param s The whole substitution.
     * @param sG The substitution restricted to ground variables.
     * @param t The source term.
     * @param c The applied clause.
     */
    public EvalResults(
        final boolean back,
        final PrologTerm b,
        final KnowledgeBase kb,
        final PrologTerm h,
        final PrologSubstitution s,
        final PrologSubstitution sG,
        final PrologTerm t,
        final PrologClause c)
    {
        this.backtrack = back;
        this.body = b;
        this.evalBase = kb;
        this.head = h;
        this.sigma = s;
        this.sigmaG = sG;
        this.term = t;
        this.toApply = c;
    }

    /**
     * @return Is backtrack case possible?
     */
    public boolean canBacktrack() {
        return this.backtrack;
    }

    /**
     * @return The target body term.
     */
    public PrologTerm getBody() {
        return this.body;
    }

    /**
     * @return The target KB.
     */
    public KnowledgeBase getEvalBase() {
        return this.evalBase;
    }

    /**
     * @return The clause head.
     */
    public PrologTerm getHead() {
        return this.head;
    }

    /**
     * @return The whole substitution.
     */
    public PrologSubstitution getSigma() {
        return this.sigma;
    }

    /**
     * @return The substitution restricted to ground variables.
     */
    public PrologSubstitution getSigmaG() {
        return this.sigmaG;
    }

    /**
     * @return The source term.
     */
    public PrologTerm getTerm() {
        return this.term;
    }

    /**
     * @return The applied clause.
     */
    public PrologClause getToApply() {
        return this.toApply;
    }

}
