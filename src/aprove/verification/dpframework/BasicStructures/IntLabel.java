package aprove.verification.dpframework.BasicStructures;

import org.w3c.dom.*;

import aprove.xml.*;

public class IntLabel implements Label {

    private final int label;

    public IntLabel(final int label){
        this.label = label;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Element toDOMLabel(final Document doc, final XMLMetaData xmlMetaData) {
        final Element l = XMLTag.LABEL.createElement(doc);
        XMLAttribute.TYPE.setAttribute(l, "integer");
        l.appendChild(XMLTag.createInteger(doc, this.label));

        return l;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return CPFTag.NUMBER.create(doc,
                doc.createTextNode("" + this.label));
    }

}
