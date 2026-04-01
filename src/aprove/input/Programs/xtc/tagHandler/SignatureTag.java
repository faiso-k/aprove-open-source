package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

public class SignatureTag implements TagHandler<XTCTagNames> {

    private final RawTrs rawtrs;

    public SignatureTag(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
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
        switch (tag) {
        case funcsym:
            return new FuncsymTag(this.rawtrs);
        default:
            throw new IllegalSubTagException(XTCTagNames.signature.toString(),
                tag.toString());
        }
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.signature,
                    attributes.getLocalName(0));
        }
    }
}
