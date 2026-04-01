package aprove.api.prooftree.impl;

import java.io.*;
import java.nio.file.*;

import aprove.cli.*;
import aprove.prooftree.Export.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Logic.*;

public enum ExportHandler {
    ;

    public static void export(ObligationNode node, Path path) throws IOException, Exception, FileNotFoundException {
        Files.deleteIfExists(path);
        doExport(node, path);
    }

    private static void doExport(ObligationNode node, Path path) throws IOException, Exception, FileNotFoundException {
        if (path.getFileName().toString().endsWith(".html")) {
            exportAsHtml(node, path);
        } else {
            exportAsNotHtml(node, path);
        }
    }

    private static void exportAsHtml(ObligationNode node, Path path) throws IOException {
        try (FileWriter out = new FileWriter(path.toFile())) {
            new ParallelHTMLExportManager(node, "problem specified in the GUI").export(out);
        }
    }

    private static void exportAsNotHtml(ObligationNode node, Path path) throws Exception,
                                                                        IOException,
                                                                        FileNotFoundException {
        try (FileOutputStream out = new FileOutputStream(path.toFile())) {
            BasicObligationNode root = (BasicObligationNode) node;
            ProofExport.exportCPF(root.getBasicObligation(),
                                  root.getTruthValue().fallbackToYNM() != YNM.fromBool(false),
                                  root,
                                  root.getTruthValue(),
                                  out);
        }
    }
}
