package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * IsFailRule.<br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
public class IsFailRule extends AbstractInferenceRule {

    /**
     * The evaluation represented as the variable which is replaced by the term to evaluate.
     */
    private final Pair<PrologTerm, PrologTerm> evaluation;

    /**
     * @param e The evaluation.
     */
    public IsFailRule(final Pair<PrologTerm, PrologTerm> e) {
        this.evaluation = e;
    }

    public Pair<PrologTerm, PrologTerm> getEvaluation() {
        return this.evaluation;
    }


    @Override
    public String prettyToString() {
        return "IS FAIL";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.IS_FAIL;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        // TODO Auto-generated method stub
        return "";
    }

    @Override
    public String toString() {
        return "IS FAIL";
    }

}
