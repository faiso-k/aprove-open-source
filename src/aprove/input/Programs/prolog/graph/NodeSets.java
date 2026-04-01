package aprove.input.Programs.prolog.graph;

import java.util.*;

import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author cryingshadow
 *
 */
public class NodeSets {

    private Set<Node<PrologAbstractState>> instanceNodes;
    private Set<Node<PrologAbstractState>> successNodes;
    private Set<Node<PrologAbstractState>> leftSplitChildren;
    private Set<Node<PrologAbstractState>> instanceChildren;
    private Set<Node<PrologAbstractState>> generalizationNodes;
    private Set<Node<PrologAbstractState>> generalizationChildren;

    public NodeSets(
        Set<Node<PrologAbstractState>> iNodes,
        Set<Node<PrologAbstractState>> gNodes,
        Set<Node<PrologAbstractState>> sNodes,
        Set<Node<PrologAbstractState>> lSpChildren,
        Set<Node<PrologAbstractState>> iChildren,
        Set<Node<PrologAbstractState>> gChildren
    ) {
        this.instanceNodes = iNodes;
        this.generalizationNodes = gNodes;
        this.successNodes = sNodes;
        this.leftSplitChildren = lSpChildren;
        this.instanceChildren = iChildren;
        this.generalizationChildren = gChildren;
    }

    public Set<Node<PrologAbstractState>> getInstanceNodes() {
        return this.instanceNodes;
    }

    public Set<Node<PrologAbstractState>> getSuccessNodes() {
        return this.successNodes;
    }

    public Set<Node<PrologAbstractState>> getLeftSplitChildren() {
        return this.leftSplitChildren;
    }

    public Set<Node<PrologAbstractState>> getInstanceChildren() {
        return this.instanceChildren;
    }

    public Set<Node<PrologAbstractState>> getGeneralizationNodes() {
        return this.generalizationNodes;
    }

    public Set<Node<PrologAbstractState>> getGeneralizationChildren() {
        return this.generalizationChildren;
    }

}
