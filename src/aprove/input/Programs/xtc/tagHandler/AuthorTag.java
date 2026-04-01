package aprove.input.Programs.xtc.tagHandler;

import org.xml.sax.*;

import aprove.input.Programs.xtc.*;
import aprove.input.Utility.XML.*;

public class AuthorTag implements TagHandler<XTCTagNames> {

    public AuthorTag() {
        // TODO Auto-generated constructor stub
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

    @Override
    public void setAttributes(Attributes attributes) {
        if (attributes.getLength() != 0) {
            throw new IllegalTagAttributeException(XTCTagNames.author,
                    attributes.getLocalName(0));
        }
    }
}
