package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.complexity.TruthValue.*;

public class MaybeTag extends Producer<ComplexityYNM> implements
        TagHandler<XTCTagNames> {

    public MaybeTag(Consumer<ComplexityYNM> parent) {
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
        throw new NoChildTagsAllowed(XTCTagNames.maybe.toString());
    }

    @Override
    public ComplexityYNM getResult() {
        return ComplexityYNM.MAYBE;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.maybe,
                    attributes.getLocalName(0));
        }
    }
}
