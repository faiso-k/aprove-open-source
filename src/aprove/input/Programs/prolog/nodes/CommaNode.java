package aprove.input.Programs.prolog.nodes;

import java.util.*;

/**
 * CommaNode.<br><br>
 *
 * Created: Oct 18, 2006<br>
 * Last modified: Oct 18, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class CommaNode extends InternalNode {

    public CommaNode(int line, int pos) {
        super(",", line, pos);
    }

    @Override
    public List<InternalNode> getChildren() {
        return null;
    }

    @Override
    public boolean addChild(InternalNode child) {
        return false;
    }

}
