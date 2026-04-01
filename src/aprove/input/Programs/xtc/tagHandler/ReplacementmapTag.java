package aprove.input.Programs.xtc.tagHandler;

import java.util.*;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class ReplacementmapTag implements TagHandler<XTCTagNames>,
        Consumer<Integer> {

    private Set<Integer> replacements = new LinkedHashSet<Integer>();

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case entry:
            return new EntryTag(this);
        default:
            throw new IllegalSubTagException(
                XTCTagNames.replacementmap.toString(), tag.toString());
        }
    }

    public Set<Integer> getReplacements() {
        return this.replacements;
    }

    @Override
    public void consume(Integer t) {
        this.replacements.add(t);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.replacementmap,
                    attributes.getLocalName(0));
        }
    }
}
