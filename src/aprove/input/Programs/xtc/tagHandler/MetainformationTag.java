package aprove.input.Programs.xtc.tagHandler;

import java.util.*;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;

public class MetainformationTag implements TagHandler<XTCTagNames>,
        Consumer<String> {

    private RawTrs rawtrs;

    private Set<String> originalFilenames = new LinkedHashSet<String>();

    public MetainformationTag(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
    }

    @Override
    public void appendCDATA(String cdata) {
    }

    @Override
    public void finish() {
        // TODO what to do with this information?
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        switch (tag) {
        case originalfilename:
            return new OriginalFilenameTag(this);
        case author:
            return new AuthorTag();
        case date:
            return new DateTag();
        case comment:
            return new CommentTag();
        default:
            throw new IllegalSubTagException(
                XTCTagNames.metainformation.toString(), tag.toString());
        }
    }

    @Override
    public void consume(String t) {
        this.originalFilenames.add(t);
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.metainformation,
                    attributes.getLocalName(0));
        }
    }
}
