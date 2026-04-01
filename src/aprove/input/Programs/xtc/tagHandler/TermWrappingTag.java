package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.BasicStructures.*;

/**
 * Can be used for {@code <lhs>}, {@code <rhs>} and other term wrapping tags.
 */
public class TermWrappingTag implements TagHandler<XTCTagNames>, Consumer<TRSTerm> {

    private XTCTagNames tag;

    public TermWrappingTag(XTCTagNames tag) {
        this.tag = tag;
    }

    private TRSTerm t;

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case funapp:
            return new FunappTag(this);
        case var:
            return new VarTag(this);
        default:
            throw new IllegalSubTagException(this.tag.toString(),
                tag.toString());
        }
    }

    @Override
    public void consume(TRSTerm t) {
        this.t = t;
    }

    @Override
    public void finish() {
    }

    public TRSTerm getTerm() {
        return this.t;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(this.tag,
                    attributes.getLocalName(0));
        }
    }
}
