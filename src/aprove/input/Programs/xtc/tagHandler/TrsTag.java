package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

public class TrsTag implements TagHandler<XTCTagNames> {

    private RawTrs rawtrs;

    public TrsTag(RawTrs rawtrs) {
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
        case rules:
            return new RulesTag(this.rawtrs);
        case signature:
            return new SignatureTag(this.rawtrs);
        case comment:
            return new CommentTag();
        case conditiontype:
            return new ConditiontypeTag(this.rawtrs);
        default:
            throw new IllegalSubTagException(XTCTagNames.trs.toString(),
                tag.toString());
        }
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.theory,
                    attributes.getLocalName(0));
        }
    }
}
