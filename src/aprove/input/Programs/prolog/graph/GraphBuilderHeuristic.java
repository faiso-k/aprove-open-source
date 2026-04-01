package aprove.input.Programs.prolog.graph;

import aprove.input.Programs.prolog.*;
import aprove.strategies.Abortions.*;

/**
 * PartEvalTreeHeuristic.<br><br>
 *
 * Created: Dec 4, 2006<br>
 * Last modified: Dec 4, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public interface GraphBuilderHeuristic {

    /**
     * Constructs a graph from the specified program.
     * @param obl The input program and query.
     * @param aborter For abortions...
     * @return The constructed graph.
     * @throws AbortionException If it is aborted...
     */
    PrologEvaluationGraph expand(PrologProblem obl, Abortion aborter) throws AbortionException;

    /**
     * @param show Set whether the constructed graph should be displayed.
     */
    void showGraph(boolean show);

    /**
     * @param show Set whether the consumed time should be displayed.
     */
    void showTime(boolean show);

}
