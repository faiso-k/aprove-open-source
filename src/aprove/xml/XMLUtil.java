package aprove.xml;

import java.io.File;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.Writer;
import java.net.URL;

import javax.xml.transform.Result;
import javax.xml.transform.Source;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMResult;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;
import javax.xml.transform.stream.StreamSource;

import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.bootstrap.DOMImplementationRegistry;
import org.w3c.dom.ls.DOMImplementationLS;
import org.w3c.dom.ls.LSOutput;
import org.w3c.dom.ls.LSSerializer;

public class XMLUtil {

    public static void transformDOMtoXML(final Document in, final Writer out) {
        // TODO test
        try {
            DOMImplementationRegistry registry = DOMImplementationRegistry.newInstance();
            DOMImplementationLS impl = (DOMImplementationLS) registry.getDOMImplementation("LS");
            LSSerializer serializer = impl.createLSSerializer();
            LSOutput output = impl.createLSOutput();
            output.setCharacterStream(out);
            serializer.write(in, output);
        } catch (final ReflectiveOperationException e) {
            e.printStackTrace();
        }
        return;
    }

    public static Node transformDocumentPerXSLT(final Document in, final Reader xsl) {
        final TransformerFactory factory = TransformerFactory.newInstance();
        final StreamSource xslSource = new StreamSource(xsl);
        Transformer transformer;
        final DOMResult output = new DOMResult();
        try {
            transformer = factory.newTransformer(xslSource);
            final Source input = new DOMSource(in.getDocumentElement());
            transformer.transform(input, output);
        } catch (final TransformerConfigurationException e) {
            e.printStackTrace();
        } catch (final TransformerException e) {
            e.printStackTrace();
        }
        return output.getNode();
    }

    public static void transformPerXSLT(final Reader in, final Writer out, final Reader xsl) {
        final TransformerFactory factory = TransformerFactory.newInstance();
        final StreamSource xslSource = new StreamSource(xsl);
        Transformer transformer;
        try {
            transformer = factory.newTransformer(xslSource);
            final Source input = new StreamSource(in);
            final Result output = new StreamResult(out);
            transformer.transform(input, output);
        } catch (final TransformerConfigurationException e) {
            e.printStackTrace();
        } catch (final TransformerException e) {
            e.printStackTrace();
        }
    }

    public static void transformPerXSLT(final File in, final Writer out, final String xsl) {
        final TransformerFactory factory = TransformerFactory.newInstance();
        final StreamSource xslSource = new StreamSource(XMLUtil.getXSLTReader(xsl), XMLUtil.class.getResource(xsl).toString());
        Transformer transformer;
        try {
            transformer = factory.newTransformer(xslSource);
            final Source input = new StreamSource(in);
            final Result output = new StreamResult(out);
            transformer.transform(input, output);
            if (aprove.Globals.DEBUG_SWISTE) {
                System.out.println("fertig");
            }
        } catch (final TransformerConfigurationException e) {
            e.printStackTrace();
        } catch (final TransformerException e) {
            e.printStackTrace();
        }
    }

    public static void transformDocumentPerXSLT(final Document in, final Writer out, final Reader xsl) {
        final TransformerFactory factory = TransformerFactory.newInstance();
        final StreamSource xslSource = new StreamSource(xsl);
        Transformer transformer;
        try {
            transformer = factory.newTransformer(xslSource);
            final Source input = new DOMSource(in.getDocumentElement());
            final Result output = new StreamResult(out);
            transformer.transform(input, output);
        } catch (final TransformerConfigurationException e) {
            e.printStackTrace();
        } catch (final TransformerException e) {
            e.printStackTrace();
        }
    }

    public static Reader getXSLTReader(final String xslt) {
        return new InputStreamReader(XMLUtil.class.getResourceAsStream(xslt));
    }

    public static URL getDTDPath(final String dtd) {
        return XMLUtil.class.getResource(dtd);
    }

}
