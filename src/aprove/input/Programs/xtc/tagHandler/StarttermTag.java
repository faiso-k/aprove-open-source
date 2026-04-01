package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

public class StarttermTag implements TagHandler<XTCTagNames> {

    private RawTrs rawtrs;

    public StarttermTag(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case constructor_based:
            return new ConstructorBasedTag(this.rawtrs);
        case full:
            return new FullTag(this.rawtrs);
        case automaton:
            // not really specified how this should work
            throw new IllegalSubTagException(XTCTagNames.problem.toString(),
                    tag.toString());
        default:
            throw new IllegalSubTagException(XTCTagNames.problem.toString(),
                    tag.toString());
        }
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.startterm,
                    attributes.getLocalName(0));
        }
    }

}
