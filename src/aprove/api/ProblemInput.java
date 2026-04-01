package aprove.api;

import java.util.*;

import aprove.api.decisions.*;

/**
 * This class represents a problem. However, further information might be required before the given problem can be analyzed:
 *
 *<br>
 * <li>If complex information needs to be supplied by the user, use {@link #createProblemDecisions()}
 *     to get a representation of the decisions that need to be made.</li>
 * <li>If only a JBC annotation is required, use {@link #withJBCAnnotation(String, String)}.</li>
 * <li>If no further information is required, call {@link #createAnalyzableProblemInput()}.</li>
 */
public interface ProblemInput {

    Optional<ProblemDecisions> createProblemDecisions() throws ProblemDecisionsInstantiationException;

    AnalyzableProblemInput withJBCAnnotation(String startMethod, String jbcAnnotations, String handlingMode);

    AnalyzableProblemInput createAnalyzableProblemInput();
}
