package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;
import aprove.verification.complexity.TruthValue.*;

public class StatusTag implements TagHandler<XTCTagNames>,
        Consumer<ComplexityYNM> {

    private RawTrs rawtrs;
    private ComplexityYNM status;

    public StatusTag(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        this.rawtrs.setStatus(this.status);
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case yes:
            return new YesTag(this);
        case no:
            return new NoTag(this);
        case maybe:
            return new MaybeTag(this);
        default:
            throw new IllegalSubTagException(XTCTagNames.status.toString(),
                tag.toString());
        }
    }

    @Override
    public void consume(ComplexityYNM status) {
        this.status = status;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.status,
                    attributes.getLocalName(0));
        }
    }
}
