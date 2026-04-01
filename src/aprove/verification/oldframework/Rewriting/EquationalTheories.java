package aprove.verification.oldframework.Rewriting ;

import java.util.*;


/** A collection of equational theories.
 *  @author Stephan Falke
 *  @version $Id$
 */

public class EquationalTheories extends LinkedHashSet<EquationalTheory> {

    private EquationalTheories() {
    super();
    }

    /** Constructor for an empty collection of equational theories.
     */
    public static EquationalTheories create() {
    return new EquationalTheories();
    }

}
