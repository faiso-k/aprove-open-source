package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.util.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public class State extends LinkedHashMap {

  public State() {
    super();
  }

  public State(int initialCapacity) {
    super(initialCapacity);
  }

  public State(int initialCapacity, float loadFactor) {
    super(initialCapacity, loadFactor);
  }

  public State(State map) {
    super(map);
  }

}
