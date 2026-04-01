package aprove.input.Programs.ttt;

import java.util.*;

import aprove.input.Generated.ttt.node.*;

/** Treewalker that collects all symbols of the term rewriting system.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

class GetSignature extends Pass {

    private Set<String> sig;

    @Override
    public void inStart(Start node) {
        this.sig = new LinkedHashSet<String>();
    }

    @Override
    public void caseTId(TId node) {
    String name = this.chop(node);
    this.sig.add(name);
    }

    public Set<String> getSignature() {
    return this.sig;
    }
}
