package aprove.cli.tpdbConverter;

import java.io.*;

import javax.xml.parsers.*;
import javax.xml.transform.*;

import aprove.exit.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotators.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;
import aprove.verification.theoremprover.ObligationFactories.*;


public class Converter {

    public static void main(String[] args) throws Exception {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(String[] args) throws ParserErrorsSourceException,
                                              SourceException,
                                              TransformerException,
                                              ParserConfigurationException,
                                              KillAproveException {
        if (args.length == 0) {
            System.err.println("converter version 1.03, please call it with input-filename");
            throw new KillAproveException(0);
        }
        if (args.length > 1) {
            System.err.println("Please call with input-filename as only argument");
            throw new KillAproveException(1);
        }
        ObligationFactory obligationFactory = new MetaObligationFactory();
        DefaultAnnotator annotator = new DefaultAnnotator();
        final Input input = new FileInput(new File(args[0]));
        final TypedInput typedInput;
        ExtensionTypeAnalyzer typeAnalyzer =  new ExtensionTypeAnalyzer();
        try {
            typedInput = typeAnalyzer.analyze(input);
        } catch (ParserErrorsSourceException e) {
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


        BasicObligation bobl =
                ((BasicObligationNode)obligationFactory.getRootAndPositions(annotatedInput).x).getBasicObligation();
        String xml = TPDB_Exporter.toXMLString(bobl, args[0]);
        System.out.println(xml);
        throw new KillAproveException(0);
    }
}
