package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * IsErrorRule.<br><br>
 *
 * @author cryingshadow
 * @version $Id$
 */
public class ArithCompFailRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "IS ERROR";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.ARITHCOMP_FAIL;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        // TODO Auto-generated method stub
        return "";
    }

    @Override
    public String toString() {
        return "IS ERROR";
    }

}
