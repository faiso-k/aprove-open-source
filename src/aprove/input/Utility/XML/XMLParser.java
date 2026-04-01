package aprove.input.Utility.XML;

import java.util.*;

import org.xml.sax.*;
import org.xml.sax.helpers.*;

/**
 * SAX Parsers suck. This makes them less painful.
 */
public abstract class XMLParser<Tags> extends DefaultHandler {

    private final Stack<TagHandler<Tags>> stack = new Stack<TagHandler<Tags>>();

    @Override
    public void startElement(String uri,
            String localName,
            String name,
            Attributes attributes) throws SAXException {
        Tags tag = this.tagFromString(name);
        TagHandler<Tags> handler;
        if (this.stack.isEmpty()) {
            handler = this.getRootHandler(tag);
        } else {
            handler = this.stack.peek().getSubHandler(tag);
        }
        handler.setAttributes(attributes);
        this.stack.push(handler);
    }

    @Override
    public void endElement(String uri, String localName, String name)
            throws SAXException {
        this.stack.pop().finish();
    }

    @Override
    public void characters(char[] ch, int start, int length)
            throws SAXException {
        this.stack.peek().appendCDATA(new String(ch, start, length));
    }

    public abstract TagHandler<Tags> getRootHandler(Tags tag)
            throws IllegalArgumentException;

    public abstract Tags tagFromString(String tagName) throws IllegalArgumentException;
}
