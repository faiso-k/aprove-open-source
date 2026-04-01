package aprove.xml;

import org.w3c.dom.*;

public class AproveDOMAttribute {

    String attName;

    public AproveDOMAttribute(String attName){
        this.attName = attName;
    }

    public void setAttribute(Element elem, String value){
        elem.setAttribute(this.attName, value);
    }

    public String getAttribute(Element elem){
        return elem.getAttribute(this.attName);
    }

    public boolean exists(Element elem){
        return elem.hasAttribute(this.attName);
    }


}
