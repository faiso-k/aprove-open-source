package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class EmptyTag implements TagHandler<XTCTagNames> {
    private XTCTagNames tag;

    EmptyTag(XTCTagNames tag) {
        this.tag = tag;
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(this.tag.toString());
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(this.tag,
                    attributes.getLocalName(0));
        }
    }
}
