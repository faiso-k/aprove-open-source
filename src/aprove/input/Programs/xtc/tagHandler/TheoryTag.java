package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class TheoryTag implements TagHandler<XTCTagNames> {

    public enum Names {
        A, C, AC;
    }

    private String theoryname = "";
    private Names theory;

    @Override
    public void appendCDATA(String cdata) {
        this.theoryname += cdata;
    }

    @Override
    public void finish() {
        this.theory = Names.valueOf(this.theoryname.trim());
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(XTCTagNames.theory.toString());
    }

    public TheoryTag.Names getTheory() {
        return this.theory;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.theory,
                    attributes.getLocalName(0));
        }
    }
}
