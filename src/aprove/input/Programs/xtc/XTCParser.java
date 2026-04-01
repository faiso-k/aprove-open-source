package aprove.input.Programs.xtc;

import java.io.*;
import java.util.*;

import org.xml.sax.*;
import org.xml.sax.helpers.*;

import aprove.input.Programs.newTrs.*;
import aprove.input.Programs.xtc.tagHandler.*;
import aprove.input.Utility.*;
import aprove.input.Utility.XML.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class XTCParser extends XMLParser<XTCTagNames> implements
        Consumer<RawTrs> {

    private RawTrs rawtrs;
    private Locator locator;

    @Override
    public TagHandler<XTCTagNames> getRootHandler(XTCTagNames tag)
            throws IllegalArgumentException {
        switch (tag) {
        case problem:
            return new ProblemTag(this);
        default:
            throw new IllegalArgumentException(
                "Expected root tag <problem> instead of <" + tag.toString()
                    + ">.");
        }
    }

    @Override
    public XTCTagNames tagFromString(String tagName)
            throws IllegalArgumentException {
        try {
            return XTCTagNames.fromString(tagName);
        } catch (IllegalArgumentException e) {
            throw new IllegalArgumentException("Unknown tag: <" + tagName + ">");
        }
    }

    @Override
    public void consume(RawTrs rawtrs) {
        this.rawtrs = rawtrs;
    }

    @Override
    public void setDocumentLocator(Locator locator) {
        this.locator = locator;
    }

    public Pair<BasicObligation, Language> parse(InputSource is)
            throws ParserError, ObligationCreatorException {
        try {
            XMLReader xr = XMLReaderFactory.createXMLReader();
            xr.setContentHandler(this);
            xr.parse(is);
        } catch (IOException e) {
            throw new ParserError(this.locator, e.getMessage());
        } catch (SAXException e) {
            throw new ParserError(this.locator, e.getMessage());
        } catch (IllegalArgumentException e) {
            throw new ParserError(this.locator, e.getMessage());
        } catch (UnsupportedOperationException e) {
            throw new ParserError(this.locator, e.getMessage());
        }

        ObligationCreator obligationCreator =
            new ObligationCreator(this.rawtrs);
        BasicObligation obl = obligationCreator.buildObligation();

        if (obl == null) {
            List<ParseError> errorMessages = obligationCreator.getErrors();
            for (ParseError er : errorMessages) {
                System.err.println(er);
            }
        }

        return new Pair<BasicObligation, Language>(obl,
            obligationCreator.getLanguage());
    }
}
