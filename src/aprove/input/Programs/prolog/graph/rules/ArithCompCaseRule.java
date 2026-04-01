package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * IsStep.<br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
public class ArithCompCaseRule extends AbstractArithmeticRule {

    public static ArithCompCaseRule createSuccessRule(final PrologTerm comparison) {
        return new ArithCompCaseRule(comparison, false);
    }

    public static ArithCompCaseRule createFailureRule(final PrologTerm comparison) {
        return new ArithCompCaseRule(comparison, true);
    }

    /**
     * A term representation of the comparison.
     */
    private final PrologTerm comparison;

    /**
     * Flag indicating whether this edge belongs to the failing branch or not.
     */
    private final boolean fail;

    /**
     * Standard constructor.
     * @param c The comparison term.
     * @param f Flag indicating whether this edge belongs to the failing branch or not.
     */
    private ArithCompCaseRule(final PrologTerm c, final boolean f) {
        this.comparison = c;
        this.fail = f;
    }

    /**
     * @return The comparison term.
     */
    public PrologTerm getComparison() {
        return this.comparison;
    }

    /**
     * @return The flag indicating whether this edge belongs to the failing branch or not.
     */
    public boolean isFail() {
        return this.fail;
    }

    @Override
    public String prettyToString() {
        return this.fail ? "ARITHCOMP FAIL" : "ARITHCOMP SUCCESS";
    }

    @Override
    public AbstractInferenceRules rule() {
        return this.fail ? AbstractInferenceRules.ARITHCOMP_FAIL : AbstractInferenceRules.ARITHCOMP_SUCCESS;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        // TODO Auto-generated method stub
        return "";
    }

    @Override
    public String toString() {
        return this.fail ? "ARITHCOMP FAIL" : "ARITHCOMP SUCCESS";
    }

}
