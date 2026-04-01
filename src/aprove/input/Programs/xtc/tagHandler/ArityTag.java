package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class ArityTag implements TagHandler<XTCTagNames> {
    String arityString = "";
    private int arity;

    @Override
    public void appendCDATA(String cdata) {
        this.arityString += cdata;
    }

    @Override
    public void finish() {
        this.arity = Integer.parseInt(this.arityString.trim());
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(XTCTagNames.arity.toString());
    }

    public int getArity() {
        return this.arity;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.arity,
                    attributes.getLocalName(0));
        }
    }
}
