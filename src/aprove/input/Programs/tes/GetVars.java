package aprove.input.Programs.tes;

import java.util.*;

import aprove.input.Generated.tes.node.*;
import aprove.verification.oldframework.Syntax.*;

/** Treewalker that collects all variables of the
 *  term rewriting system.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

class GetVars extends Pass {

    private Hashtable vars = new Hashtable();

    @Override
    public void inAConstVarPrefixterm(AConstVarPrefixterm node) {
    String name = this.chop(node.getId());
    if (this.gvars.contains(name)) {
        this.vars.put(name, VariableSymbol.create(name, this.poly));
    }
    }

    public Map getTermVars() {
    return this.vars;
    }
}
