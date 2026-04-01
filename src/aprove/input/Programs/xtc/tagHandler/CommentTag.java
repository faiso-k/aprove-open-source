package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class CommentTag implements TagHandler<XTCTagNames> {
    @Override
    public void appendCDATA(String cdata) {
        // ignore
    }

    @Override
    public void finish() {
    }

    @Override
    public TagHandler<XTCTagNames> getSubHandler(XTCTagNames tag)
            throws IllegalArgumentException, UnsupportedOperationException {
        throw new IllegalSubTagException(XTCTagNames.comment.toString(),
                tag.toString());
    }

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.comment,
                    attributes.getLocalName(0));
        }
    }
}
