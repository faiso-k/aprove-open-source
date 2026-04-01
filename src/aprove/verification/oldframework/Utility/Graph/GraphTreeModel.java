package aprove.verification.oldframework.Utility.Graph;

import java.util.*;

import javax.swing.event.*;
import javax.swing.tree.*;

/**
 * This class wraps a Graph into a tree model for
 * display in a JTree component.
 *
 * @author Peter Schneider-Kamp
 * @version $Id$
 */
public class GraphTreeModel implements TreeModel {

    Graph g;
    Object root;
    List listeners;

    public GraphTreeModel(Graph g) {
        Set<Cycle> sccs = g.getSCCs();
        Iterator i = sccs.iterator();
        while (i.hasNext()) {
            Set<Node> scc = (Set<Node>)i.next();
            if (scc.size() > 1) {
                throw new RuntimeException("Internal error: graph is not a tree.");
            }
        }
        this.g = g;
        this.root = null;
        this.listeners = new Vector();
    }

    public Graph getGraph() {
        return this.g;
    }

    @Override
    public void addTreeModelListener(TreeModelListener l) {
        this.listeners.add(l);
    }
    @Override
    public void removeTreeModelListener(TreeModelListener l) {
        this.listeners.remove(l);
    }
    @Override
    public void valueForPathChanged(TreePath path, Object newValue) {
    }

    private Set<Node> getOut(Object parent) {
        Set<Node> outs = new LinkedHashSet<Node>(this.g.getOut((Node)parent));
        outs.remove(parent);
        return outs;
    }
    private Set<Node> getIn(Object child) {
        Set<Node> ins = new LinkedHashSet<Node>(this.g.getIn((Node)child));
        ins.remove(child);
        return ins;
    }
    @Override
    public Object getChild(Object parent, int index) {
        Object child = null;
        Iterator i = this.getOut(parent).iterator();
        for (int count = 0; count <= index; count++) {
            if (i.hasNext()) {
                child = i.next();
            } else {
                return null;
            }
        }
        return child;
    }
    @Override
    public int getChildCount(Object parent) {
        return this.getOut(parent).size();
    }
    @Override
    public int getIndexOfChild(Object parent, Object child) {
        Iterator i = this.getOut(parent).iterator();
        int count = 0;
        while (i.hasNext()) {
            if (child.equals(i.next())) {
                return count;
            }
            count++;
        }
        return -1;
    }

    @Override
    public Object getRoot() {
        if (this.root == null) {
            Iterator i = this.g.getNodes().iterator();
            while (i.hasNext()) {
                Object node = i.next();
                Set<Node> in = this.getIn(node);
                if (in.size() == 0) {
                    this.root = node;
                    break;
                }
            }
        }
        return this.root;
    }
    @Override
    public boolean isLeaf(Object node) {
        Set<Node> out = this.getOut(node);
        int size = out.size();
        return size == 0;
    }

}
