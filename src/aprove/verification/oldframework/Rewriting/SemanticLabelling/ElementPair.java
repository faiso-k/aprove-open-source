package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.util.*;

public class ElementPair {

    private List<ElementValue> left;
    private List<ElementValue> right;

    public ElementPair(List<ElementValue> left, List<ElementValue> right) {

    this.left = left;
    this.right = right;

    }

    public List<ElementValue> getLeft() {

    return this.left;

    }

    public List<ElementValue> getRight() {

    return this.right;

    }

    public String getLeftLabel() {

    String label = "";
    Iterator iter = this.left.iterator();
    while (iter.hasNext()) {
        label += ((ElementValue) iter.next()).getLabel();
    }
    return label;

    }

    public String getRightLabel() {

    String label = "";
    Iterator iter = this.right.iterator();
    while (iter.hasNext()) {
        label += ((ElementValue) iter.next()).getLabel();
    }
    return label;

    }

    @Override
    public boolean equals(Object obj) {

    if (obj instanceof ElementPair) {
        ElementPair pair = (ElementPair) obj;
        if (pair.left.equals(this.left) && pair.right.equals(this.right)) {
        return true;
        }
    }
    return false;

    }

    @Override
    public int hashCode() {

    return this.left.hashCode() + this.right.hashCode();

    }

    @Override
    public String toString() {

    String s = "[";
    Iterator li = this.left.iterator();
    while (li.hasNext()) {
        s += li.next().toString() ;
    }
    s += ", ";
    Iterator ri = this.right.iterator();
    while (ri.hasNext()) {
        s += ri.next().toString() ;
    }
    s += "]";
    return s;

    }

}
