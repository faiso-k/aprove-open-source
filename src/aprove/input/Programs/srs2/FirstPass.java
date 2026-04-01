/**
 *
 * @author Christoph Weidmann
 * @version $Id$
 */
package aprove.input.Programs.srs2;

import java.util.*;

import aprove.input.Generated.srs2.analysis.*;
import aprove.input.Generated.srs2.node.*;

// This class traverses the AST and collects the names of the
// function symbols encountered in word-nodes in the set fnames

public class FirstPass extends DepthFirstAdapter {

    private Set<String> fnames = new LinkedHashSet<String>(); // to store the names of the function symbols

    @Override
    public void inAOneWord(AOneWord node)
    {
        this.defaultIn(node);
    }

    // When leaving a OneWord-Node,
    // add the name of the function symbol to the set.
    // Alternatively, we could do this when entering the node.
    @Override
    public void outAOneWord(AOneWord node)
    {
        this.fnames.add(node.getId().getText().trim());
    }

    @Override
    public void inAMoreWord(AMoreWord node)
    {
        this.defaultIn(node);
    }

    // When leaving a MoreWord-Node,
    // add the name of the function symbol to the set
    @Override
    public void outAMoreWord(AMoreWord node)
    {
        this.fnames.add(node.getId().getText().trim());
    }
    public Set<String> getFunctionSymbolNames() {
        return this.fnames;
    }

}
