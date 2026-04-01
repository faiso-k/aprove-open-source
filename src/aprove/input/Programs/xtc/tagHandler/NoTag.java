package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.complexity.TruthValue.*;

public class NoTag extends Producer<ComplexityYNM> implements
        TagHandler<XTCTagNames> {

    public NoTag(Consumer<ComplexityYNM> parent) {
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
        throw new NoChildTagsAllowed(XTCTagNames.no.toString());
    }

    @Override
    public ComplexityYNM getResult() {
        return ComplexityYNM.createLower(ComplexityValue.infinite());
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.no,
                    attributes.getLocalName(0));
        }
    }
}
