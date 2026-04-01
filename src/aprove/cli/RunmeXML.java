package aprove.cli;

import java.io.*;
import java.util.*;

import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;

import org.w3c.dom.*;

import aprove.exit.*;
import aprove.input.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotators.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.ObligationFactories.*;
import aprove.xml.*;

public class RunmeXML {
    public static void main(String[] args) throws Exception {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(String[] args) throws ParserErrorsSourceException,
                                              SourceException,
                                              InterruptedException,
                                              ParserConfigurationException,
                                              TransformerFactoryConfigurationError,
                                              TransformerConfigurationException,
                                              TransformerException,
                                              KillAproveException {
        ObligationFactory obligationFactory = new MetaObligationFactory();
        DefaultAnnotator annotator = new DefaultAnnotator();
        final Input input = new FileInput(new File(args[0]));
        final TypedInput typedInput;
        ExtensionTypeAnalyzer typeAnalyzer =  new ExtensionTypeAnalyzer();
        try {
            typedInput = typeAnalyzer.analyze(input);
        } catch (ParserErrorsSourceException e) {
//            callRelease12(argv);
            System.err.println("ERROR\nError while parsing");
            throw new KillAproveException(1);
        }

        final AnnotatedInput annotatedInput;
        try {
            annotatedInput = annotator.annotate(typedInput);
        } catch (SourceException e) {
            System.err.println("ERROR\nError while annotating ");
            throw new KillAproveException(1);
        }


        Pair<ObligationNode, List<BasicObligationNode>> rootAndPositions =
                obligationFactory.getRootAndPositions(annotatedInput);
        final ObligationNode root = rootAndPositions.x;
        UserStrategy startStrategy = new VariableStrategy("main");

        final StrategyProgram program;
        // programInput = EasyInput.loadStrategyModule(args[1]);
        if (args.length == 1) {
            program = EasyInput.parseStrategy("main = QTRSDependencyPairs:RepeatS(0,*,First(QDPDependencyGraph:Maybe(QDPNonSCC),QDPPolo[Engine=MINISAT,Range=3]))");
        } else if (args[1].equals("-ng")) {
            program = EasyInput.parseStrategy("main = QTRSDependencyPairs:RepeatS(0,*,QDPPolo[Engine=SAT4J])");
        } else {
            program = EasyInput.parseStrategy("main = QTRSDependencyPairs:RepeatS(0,*,"+args[1]+")");
        }

        final StrategyExecutionHandle handle = Machine.theMachine.start(
                startStrategy, program, rootAndPositions.y, null);

        // wait for the machine to finish
        try {
            handle.waitForFinish();
        } catch (InterruptedException e) {
            System.err.println("ERROR\nunexpected interruption while running machine");
            throw e;
        }

        if (root.isTruthValueKnown()) {
            DocumentBuilderFactory docFact = DocumentBuilderFactory.newInstance();
            Document doc = docFact.newDocumentBuilder().newDocument();
            XMLMetaData xmlMetaData = XMLMetaData.createEmptyMetaData();
            Element e = root.toDOM(doc, xmlMetaData);
            doc.appendChild(e);
            TransformerFactory transformerFactory = TransformerFactory.newInstance();
            Transformer transformer = transformerFactory.newTransformer();
            DOMSource source = new DOMSource(doc);
            StreamResult result =  new StreamResult(System.out);
            transformer.transform(source, result);
            throw new KillAproveException(0);
        } else {
            throw new KillAproveException(1);
        }
    }
}
