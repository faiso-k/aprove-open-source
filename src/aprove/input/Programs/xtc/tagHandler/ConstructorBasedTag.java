package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

public class ConstructorBasedTag implements TagHandler<XTCTagNames> {

    private RawTrs rawtrs;

    public ConstructorBasedTag(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new IllegalSubTagException(XTCTagNames.problem.toString(),
                tag.toString());
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        this.rawtrs.setConstructorbased(true);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.constructor_based,
                    attributes.getLocalName(0));
        }
    }
}
