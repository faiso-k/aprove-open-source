package aprove.cli;

import java.io.*;

import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.verification.diophantine.*;
import aprove.verification.oldframework.CPF.*;
import aprove.verification.oldframework.Logic.*;
import aprove.xml.*;

public enum ProofExport {

    CPF {
        @Override
        public void export(final ObligationNode root, final String filename) throws Exception {
            final BasicObligationNode broot = (BasicObligationNode) root;
            broot.writeCPF(System.out);
        }
    },

    DIO_CIME {
        @Override
        public void export(final ObligationNode root, final String filename) {
            if (root.getSuccessorCount() != 1 || !(root instanceof BasicObligationNode)) {
                System.err.println("Diophantine cime: No proof or weird proof, giving up.");
                return;
            }
            //We know that we put in a BasicObligation as root:
            final BasicObligationNode basOblRoot = (BasicObligationNode) root;
            final Proof proof = basOblRoot.getSuccessors().get(0).getProof();
            if (! (proof instanceof DiophantineProcessor.DiophantineProof)) {
                System.err.println("Diophantine cime: No dio-proof, giving up.");
            }

            System.out.println(((DiophantineProcessor.DiophantineProof)proof).toCime());
        }
    },

    HTML {
        @Override
        public void export(final ObligationNode root, final String filename) {
            new ParallelHTMLExportManager(root, filename)
                    .exportToStdOut();
        }
    },

    LATEX {
        @Override
        public void export(final ObligationNode root, final String filename) {
            throw new UnsupportedOperationException(
                    "LaTeX-Export was never implemented!");
        }
    },

    NONE {
        @Override
        public void export(final ObligationNode root, final String filename) {
            // Do nothing.
        }
    },

    OLDHTML {
        @Override
        public void export(final ObligationNode root, final String filename) {
            final String htmlProof = new GenericExportManager(root, filename,
                    false).export(new HTML_Util());
            System.out.println(htmlProof);
        }
    },

    OLDPLAIN {
        @Override
        public void export(final ObligationNode root, final String filename) {
            System.out.println(new GenericExportManager(root, filename, false)
                    .export(new PLAIN_Util()));
        }
    },

    PLAIN {
        @Override
        public void export(final ObligationNode root, final String filename) {
            new ParallelPlainExportManager(root, filename)
                    .exportToStdOut();
        }
    },

    XML {
        @Override
        public void export(final ObligationNode root, final String filename)
                throws Exception {
            final DocumentBuilderFactory docFact = DocumentBuilderFactory
                    .newInstance();
            final Document doc = docFact.newDocumentBuilder().newDocument();
            final XMLMetaData xmlMetaData = XMLMetaData.createEmptyMetaData();
            final Element e = root.toDOM(doc, xmlMetaData);
            doc.appendChild(e);
            final TransformerFactory transformerFactory = TransformerFactory
                    .newInstance();
            final Transformer transformer = transformerFactory.newTransformer();
            final DOMSource source = new DOMSource(doc);
            final StreamResult result = new StreamResult(System.out);
            transformer.transform(source, result);
        }
    };

    public static void exportCPF(
        final CPFInputProblem input,
        final boolean positive,
        final CPFObligationNode proof,
        final TruthValue tv,
        final OutputStream stream
    ) throws Exception {
        final DocumentBuilderFactory docFact = DocumentBuilderFactory.newInstance();
        final Document doc = docFact.newDocumentBuilder().newDocument();
        final XMLMetaData xmlMetaData = XMLMetaData.createEmptyMetaData();
        final CPFExportStatistic statistic = new CPFExportStatistic();
        final Element problem =
            CPFTag.CERTIFICATION_PROBLEM.create(
                doc,
                CPFTag.INPUT.create(doc, input.getCPFInput(doc, xmlMetaData, tv)),
                CPFTag.CPF_VERSION.create(doc, doc.createTextNode("2.1")),
                CPFTag.PROOF.create(doc, proof.toCPF(doc, positive, xmlMetaData, statistic))
            );
        final Element origin = CPFTag.ORIGIN.createElement(doc);
        final Element proofOrigin = CPFTag.PROOF_ORIGIN.createElement(doc);
        final Element tool = CPFTag.TOOL.createElement(doc);
        final Element name = CPFTag.NAME.createElement(doc);
        name.appendChild(doc.createTextNode("AProVE"));
        final String versionString = ExportManager.getCommitDescriptionText();
        final Element version = CPFTag.VERSION.create(doc, doc.createTextNode(versionString));
        final Element strategy = CPFTag.STRATEGY.create(doc, doc.createTextNode(statistic.toString()));
        final Element url = CPFTag.URL.createElement(doc);
        url.appendChild(doc.createTextNode("http://aprove.informatik.rwth-aachen.de"));
        tool.appendChild(name);
        tool.appendChild(version);
        tool.appendChild(strategy);
        tool.appendChild(url);
        final Element toolUser = CPFTag.TOOL_USER.createElement(doc);
        final Element firstName = CPFTag.FIRST_NAME.createElement(doc);
        firstName.appendChild(doc.createTextNode("John"));
        final Element lastName = CPFTag.LAST_NAME.createElement(doc);
        lastName.appendChild(doc.createTextNode("Doe"));
        toolUser.appendChild(firstName);
        toolUser.appendChild(lastName);
        proofOrigin.appendChild(tool);
        proofOrigin.appendChild(toolUser);
        final Element inputOrigin = CPFTag.INPUT_ORIGIN.createElement(doc);
        origin.appendChild(proofOrigin);
        origin.appendChild(inputOrigin);
        problem.appendChild(origin);

        doc.appendChild(problem);
        final TransformerFactory transformerFactory = TransformerFactory.newInstance();
        final Transformer transformer = transformerFactory.newTransformer();
        transformer.setOutputProperty(OutputKeys.INDENT, "no");
        transformer.setOutputProperty(OutputKeys.ENCODING, "UTF-8");
        transformer.setOutputProperty(OutputKeys.METHOD, "xml");
        doc.getDocumentElement().setAttribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance");
        doc.getDocumentElement().setAttribute("xsi:noNamespaceSchemaLocation", "cpf.xsd");
        doc.insertBefore(
            doc.createProcessingInstruction("xml-stylesheet", "type=\"text/xsl\" href=\"cpfHTML.xsl\""),
            doc.getDocumentElement()
        );
        final DOMSource source = new DOMSource(doc);
        final StreamResult result = new StreamResult(stream);
        transformer.transform(source, result);
    }

    public abstract void export(ObligationNode root, String filename) throws Exception;

}
