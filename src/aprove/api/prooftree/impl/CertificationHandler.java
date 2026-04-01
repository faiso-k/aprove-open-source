package aprove.api.prooftree.impl;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.atomic.*;

import javax.xml.parsers.*;

import org.w3c.dom.*;

import aprove.api.prooftree.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.verification.oldframework.CPF.*;
import aprove.verification.oldframework.Logic.*;
import aprove.xml.*;

public enum CertificationHandler {
    ;

    // TODO remove global state
    private static final AtomicInteger onlineCheckerCounter = new AtomicInteger(0);
    private static final CPFOnlineChecker onlineChecker = createOnlineChecker();

    private static CPFOnlineChecker createOnlineChecker() {
        try {
            return CPFOnlineChecker.createCPFOnlineChecker(Files.createTempDirectory("GUI"));
        } catch (IOException e) {
            return null;
        }
    }

    public static void onlineCertificationPath(Optional<Path> onlineCertificationPath) {
        Options.onlineCertification = onlineCertificationPath.map(Path::toString).orElse(null);
    }

    public static void setOnlineChecker(String prefix) {
        if (Options.onlineCertification != null) {
            BasicObligationNode.setCPFOnlineChecker(CPFOnlineChecker.createCPFOnlineChecker(Options.onlineCertification,
                                                                                            prefix));
        } else {
            BasicObligationNode.setCPFOnlineChecker(null);
        }
    }

    public static CertificationResult certify(ObligationNode obl) {
        CPFCheckResult checkResult = getCheckResult(obl);
        int[] numbers = getNumbers(obl);
        return new CertificationResultImpl(checkResult, numbers[0], numbers[1], numbers[2]);
    }

    private static CPFCheckResult getCheckResult(ObligationNode obl) {
        if (onlineChecker != null) {
            int i = onlineCheckerCounter.incrementAndGet();
            String filename = onlineChecker.getFileName(i + "");
            new File(filename).deleteOnExit();
            return obl.checkProof(filename).x;
        } else {
            // could not generate file
            return CPFCheckResult.ErrorWhenGeneratingCPF;
        }
    }

    private static int[] getNumbers(ObligationNode obl) {
        Optional<Document> doc = getDoc();
        if (doc.isPresent()) {
            CPFExportStatistic statistic = new CPFExportStatistic();
            obl.toCPF(doc.get(),
                      obl.getTruthValue().fallbackToYNM() != YNM.fromBool(false),
                      XMLMetaData.createEmptyMetaData(),
                      statistic);
            return new int[] { statistic.getNrRealProofs(),
                               statistic.getNrAssumptions(),
                               statistic.getNrUnknownProofs() };
        } else {
            return new int[] { -1, -1, -1 };
        }
    }

    private static Optional<Document> getDoc() {
        try {
            return Optional.of(DocumentBuilderFactory.newInstance().newDocumentBuilder().newDocument());
        } catch (ParserConfigurationException e) {
            e.printStackTrace();
            return Optional.empty();
        }
    }
}
