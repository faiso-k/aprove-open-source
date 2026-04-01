package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * IsStep.<br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
public class IsCaseRule extends AbstractArithmeticRule {

    /**
     * The evaluation represented as the variable which is replaced by the term to evaluate.
     */
    private final Pair<PrologAbstractVariable, PrologTerm> evaluation;

    /**
     * The substitution. Null indicates failing branch.
     */
    private final PrologSubstitution substitution;

    /**
     * Constructor for failing branch.
     */
    public IsCaseRule() {
        this(null, null);
    }

    /**
     * @param s The substitution.
     * @param e The evaluation.
     */
    public IsCaseRule(final PrologSubstitution s, final Pair<PrologAbstractVariable, PrologTerm> e) {
        this.substitution = s;
        this.evaluation = e;
    }

    /**
     * @return The evaluation.
     */
    public Pair<PrologAbstractVariable, PrologTerm> getEvaluation() {
        return this.evaluation;
    }

    /**
     * @return The substitution.
     */
    public PrologSubstitution getSubstitution() {
        return this.substitution;
    }

    @Override
    public String prettyToString() {
        return this.getSubstitution() == null ? "IS FAIL" : "IS SUCCESS"
            + "\\n"
            + this.getSubstitution().prettyToString();
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.IS_CASE;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        // TODO Auto-generated method stub
        return "";
    }

    @Override
    public String toString() {
        return this.getSubstitution() == null ? "IS FAIL" : "IS SUCCESS" + "\n" + this.getSubstitution().toString();
    }

}
