package aprove.input.Programs.prolog.graph;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;

/**
 * GroundnessAnalysis.<br><br>
 *
 * Created: Sep 22, 2008<br>
 * Last modified: Sep 22, 2008
 *
 * @author cryingshadow
 * @version $Id$
 */
public interface GroundnessAnalysis {

    /**
     * Calculates which positions will become ground if the specified positions are instantiated by ground terms.
     * @param predicate The predicate to consider.
     * @param groundPositions The initial ground positions.
     * @return The positions which will become ground after an arbitrary successful evaluation.
     */
    Set<Integer> getGroundPositions(FunctionSymbol predicate, Set<Integer> groundPositions);

}
