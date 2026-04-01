package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.dpframework.BasicStructures.*;

public class ArgTag extends Producer<TRSTerm> implements TagHandler<XTCTagNames>,
        Consumer<TRSTerm> {

    public ArgTag(Consumer<TRSTerm> parent) {
        super(parent);
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        this.produce();
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
            throw new IllegalSubTagException(XTCTagNames.arg.toString(),
                tag.toString());
        }
    }

    TRSTerm t;

    @Override
    public TRSTerm getResult() {
        return this.t;
    }

    @Override
    public void consume(TRSTerm t) {
        this.t = t;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.arg,
                    attributes.getLocalName(0));
        }
    }
}
