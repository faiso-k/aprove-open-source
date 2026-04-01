package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;
import aprove.verification.complexity.TruthValue.*;

/**
 * Handler for {@code <upperbound>} and {@code <lowerbound>}.
 */
public class BoundTag implements TagHandler<XTCTagNames> {

    private XTCTagNames tag;

    public BoundTag (XTCTagNames tag) {
        this.tag = tag;
    }

    @Override
    public void appendCDATA(String cdata) {
        // TODO Auto-generated method stub

    }

    @Override
    public void finish() {
        // TODO Auto-generated method stub

    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        // TODO Auto-generated method stub
        return null;
    }

    public ComplexityValue getBound() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(this.tag,
                    attributes.getLocalName(0));
        }
    }
}
