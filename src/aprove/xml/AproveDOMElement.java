package aprove.xml;

import org.w3c.dom.*;

public class AproveDOMElement {

    String tagName;

    public AproveDOMElement(String tagName){
        this.tagName = tagName;
    }

    public Element createElement(Document doc, Node parent){
        Element node = this.createElement(doc);
        if (parent != null) {
            parent.appendChild(node);
        }
        return node;
    }

    public Element createElement(Document doc){
        return doc.createElement(this.tagName);
    }

    public boolean recognize(Node node, Short nodeType){
        return (this.tagName.equals(node.getNodeName()) && node.getNodeType() == nodeType);
    }

    public boolean recognize(Node node){
        if (node != null && node.getNodeName() != null) {
            return (this.tagName.equals(node.getNodeName()) && node.getNodeType() == Node.ELEMENT_NODE);
        } else {
            return false;
        }
    }
}