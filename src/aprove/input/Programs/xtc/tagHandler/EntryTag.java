package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class EntryTag extends Producer<Integer> implements
        TagHandler<XTCTagNames> {

    public EntryTag(Consumer<Integer> parent) {
        super(parent);
    }

    private String intString = "";

    @Override
    public void appendCDATA(String cdata) {
        this.intString += cdata;
    }

    @Override
    public void finish() {
        this.produce();
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new NoChildTagsAllowed(XTCTagNames.entry.toString());
    }

    @Override
    public Integer getResult() {
        return Integer.parseInt(this.intString.trim());
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.entry,
                    attributes.getLocalName(0));
        }
    }
}
