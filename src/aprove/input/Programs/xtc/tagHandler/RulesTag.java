package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

public class RulesTag implements TagHandler<XTCTagNames> {

    private RawTrs rawtrs;

    public RulesTag(RawTrs rawtrs) {
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
        case rule:
            return new RuleTag(this.rawtrs, false);
        case relrules:
            return new RelrulesTag(this.rawtrs);
        default:
            throw new IllegalSubTagException(XTCTagNames.rules.toString(),
                tag.toString());
        }
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.rules,
                    attributes.getLocalName(0));
        }
    }
}
