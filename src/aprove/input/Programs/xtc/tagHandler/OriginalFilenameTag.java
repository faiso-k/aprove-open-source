package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class OriginalFilenameTag extends Producer<String> implements
        TagHandler<XTCTagNames> {

    private String filename = "";

    public OriginalFilenameTag(Consumer<String> parent) {
        super(parent);
    }

    @Override
    public void appendCDATA(String cdata) {
        this.filename += cdata;
    }

    @Override
    public void finish() {
        this.produce();
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(XTCTagNames.originalfilename.toString());
    }

    @Override
    public String getResult() {
        return this.filename;
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.originalfilename,
                    attributes.getLocalName(0));
        }
    }
}
