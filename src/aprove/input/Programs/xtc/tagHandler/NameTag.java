package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class NameTag implements TagHandler<XTCTagNames> {
    private String name = "";

    @Override
    public void appendCDATA(String cdata) {
        this.name += cdata;
    }

    public String getName() {
        return this.name;
    }

    @Override
    public void finish() {
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(XTCTagNames.name.toString());
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.name,
                    attributes.getLocalName(0));
        }
    }
}
