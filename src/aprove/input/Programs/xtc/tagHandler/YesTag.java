package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.complexity.TruthValue.*;

public class YesTag extends Producer<ComplexityYNM> implements
        TagHandler<XTCTagNames> {

    public YesTag(Consumer<ComplexityYNM> parent) {
        super(parent);
    }

    private BoundTag lowerboundTag;
    private BoundTag upperboundTag;

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
        case lowerbound:
            this.lowerboundTag = new BoundTag(tag);
            return this.lowerboundTag;
        case upperbound:
            this.upperboundTag = new BoundTag(tag);
            return this.upperboundTag;
        default:
            throw new IllegalSubTagException(XTCTagNames.yes.toString(),
                tag.toString());
        }
    }

    @Override
    public ComplexityYNM getResult() {
        ComplexityValue lower = ComplexityValue.constant();
        ComplexityValue upper = ComplexityValue.infinite();

        if (this.lowerboundTag != null) {
            lower = this.lowerboundTag.getBound();
        }
        if (this.upperboundTag != null) {
            upper = this.upperboundTag.getBound();
        }

        return ComplexityYNM.create(lower, upper);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.yes,
                    attributes.getLocalName(0));
        }
    }
}
