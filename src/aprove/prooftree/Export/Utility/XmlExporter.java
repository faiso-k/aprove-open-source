package aprove.prooftree.Export.Utility;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;

import org.jdom.*;
import org.jdom.output.*;

/**
 * Every class that wants to be exported to XML must use this
 * class.
 *
 * This "uses" relation is of course suboptimal. A better
 * solution would be to integrate the XML functionality into the
 * class hierarchy, but this required refactoring.
 *
 * @author Tim Rohlfs
 *
 */
public class XmlExporter {

    public static XmlExporter create(final XmlExportable exportable) {
        final XmlExporter exporter = new XmlExporter(exportable);
        return exporter;
    }

    protected static final TransformerFactory tFactory = TransformerFactory.newInstance();

    private static final String PLAIN_TEMPLATE_SOURCE = "src/aprove/ProofTree/Export/Utility/idp2-output-transformer.xslt";;

    protected static final Templates PLAIN_TEMPLATE;
    static {
        Templates template = null;

        try {
            template  = XmlExporter.tFactory.newTemplates(new StreamSource(new FileInputStream(XmlExporter.PLAIN_TEMPLATE_SOURCE)));
        } catch (final TransformerConfigurationException e) {
            e.printStackTrace();
        } catch (final FileNotFoundException e) {
            System.out.println("IDP XML-Export: can not find XSLT for PLAIN output: " + XmlExporter.PLAIN_TEMPLATE_SOURCE);
        }

        PLAIN_TEMPLATE = template;
    }

    protected Document document;
    protected Element rootElement;

    protected Transformer transformer;

    protected XmlExporter(final XmlExportable owner) {
        this.document = new Document(this.recurse(owner));
        try {
            this.transformer = XmlExporter.PLAIN_TEMPLATE.newTransformer();
//            transformer = tFactory.newTransformer();

            this.transformer.setOutputProperty(OutputKeys.INDENT, "no");
        } catch (final TransformerConfigurationException e) {
            e.printStackTrace();
        }
    }

    protected Element recurse(final XmlExportable node) {
        final Element e = new Element(node.getClass().getSimpleName());

        final Map<String, String> attribs = node.getXmlAttribs(this);
        final XmlContentsMap contents = node.getXmlContents(this);

        if (attribs != null) {
            for (final Entry<String, String> attrib : attribs.entrySet()) {
                e.setAttribute(new Attribute(attrib.getKey(), attrib.getValue()));
            }
        }

        if (contents != null) {
            if (contents.isEmpty()) {
                e.setText(node.toString());
            } else {
                for (final XmlContentsEntry obj : contents) {
                    final String name = obj.getName();

                    if (!name.isEmpty()) {
                        final Element element = new Element(name);

                        final Map<String, String> entryAttribs = obj.getAttribs();
                        if (entryAttribs != null) {
                            for (final Entry<String, String> attrib : entryAttribs.entrySet()) {
                                element.setAttribute(attrib.getKey(), attrib.getValue());
                            }
                        }

                        element.addContent(this.recurse(obj.getExportable()));
                        e.addContent(element);
                    } else {
                        e.addContent(this.recurse(obj.getExportable()));
                    }
                }
            }
        }

        return e;
    }

    public synchronized void export(final StringBuilder sb) throws Exception {
        if (this.transformer == null) {
            throw new Exception("Cannot transform XML: XSLT was not set");
        }

        final DOMOutputter outputter = new org.jdom.output.DOMOutputter();
        final org.w3c.dom.Document domDocument = outputter.output(this.document);
           final Source source = new DOMSource(domDocument);
           final StreamResult outputStream = new StreamResult();
           final StringWriter writer = new StringWriter();
           outputStream.setWriter(writer);
           this.transformer.transform(source, outputStream);
           sb.append(writer.toString());
    }

    @Override
    public synchronized String toString() {
        final XMLOutputter xout = new XMLOutputter();
        xout.setFormat(Format.getPrettyFormat());
        final OutputStream stream = new StringStream();

        try {
            xout.output(this.document, stream);
        } catch (final IOException e) {
            System.err.println("Could not output the XML data into the stream.");
            return this.document.toString();
        }

        return stream.toString();
    }
}