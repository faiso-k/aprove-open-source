package aprove.verification.oldframework.CPF;

import java.io.*;
import java.nio.file.*;
import java.util.concurrent.atomic.*;
import java.util.logging.*;

/**
 * Statistics and data for CPF-Online-Checking,
 * i.e., during proof generation.
 */
public class CPFOnlineChecker {

    public static Logger log = java.util.logging.Logger.getLogger("CPFOnlineChecking");

    private AtomicInteger certUnknownProofStructure, certUnsupportedAprove, certRejected, certAccepted,
            certUnsupported, certNrProofSteps, certNrImplications, certProblemExport, certProblemExecCertifier;
    private Path onlineCertPath;

    public String getFileName(final String name) {
        return Paths.get(this.onlineCertPath.toString(), name).toString();
    }

    public int getNrUnsupportedByCeTA() {
        return this.certUnsupported.get();
    }

    public int getNrRejectedByCeTA() {
        return this.certRejected.get();
    }

    public int getNrAcceptedByCeTA() {
        return this.certAccepted.get();
    }

    public int getNrOfAnalyzedProofSteps() {
        return this.certNrImplications.get();
    }

    public int getNrOfUnknownProofSteps() {
        return this.certUnsupportedAprove.get();
    }

    public int getNrOfProblems() {
        return this.certProblemExecCertifier.get() + this.certProblemExport.get();
    }

    public int incrementUnknownProofStructure() {
        return this.certUnknownProofStructure.incrementAndGet();
    }

    public int incrementUnsupportedAprove() {
        return this.certUnsupportedAprove.incrementAndGet();
    }

    public int incrementRejected() {
        return this.certRejected.incrementAndGet();
    }

    public int incrementAccepted() {
        return this.certAccepted.incrementAndGet();
    }

    public int incrementUnsupported() {
        return this.certUnsupported.incrementAndGet();
    }

    public int incrementNrProofSteps() {
        return this.certNrProofSteps.incrementAndGet();
    }

    public int incrementNrImplications() {
        return this.certNrImplications.incrementAndGet();
    }

    public int incrementProblemExport() {
        return this.certProblemExport.incrementAndGet();
    }

    public int incrementProblemExecCertifier() {
        return this.certProblemExecCertifier.incrementAndGet();
    }

    /**
     * creates a CPFOnlineChecker
     * @param directory - where to store the proofs, e.g., tmp/onlineCPFs
     * @param prefix - prefix for file names, e.g. AG01/3.1
     * @return an CPFOnlineChecker, if everything works fine, i.e., if the directories exist and ceta is available,
     *   or null, in case of an error.
     * @throws IOException
     */
    public static CPFOnlineChecker
            createCPFOnlineChecker(final String directory, final String prefix) {
        if (directory == null || prefix == null) {
            return null;
        }
        try {
            Path onlineCertPath = Files.createDirectories(Paths.get(directory, prefix));
            return CPFOnlineChecker.createCPFOnlineChecker(onlineCertPath);
        } catch (final IOException e) {
            CPFOnlineChecker.log.log(Level.WARNING, "could not create directory for online certification");
            return null;
        }
    }

    public static CPFOnlineChecker createCPFOnlineChecker(Path onlineCertPath) {
        final CPFOnlineChecker checker = new CPFOnlineChecker();
        boolean active = false;
            checker.certUnknownProofStructure = new AtomicInteger(0);
            checker.certUnsupportedAprove = new AtomicInteger(0);
            checker.certRejected = new AtomicInteger(0);
            checker.certAccepted = new AtomicInteger(0);
            checker.certUnsupported = new AtomicInteger(0);
            checker.certNrProofSteps = new AtomicInteger(0);
            checker.certNrImplications = new AtomicInteger(0);
            checker.certProblemExport = new AtomicInteger(0);
            checker.certProblemExecCertifier = new AtomicInteger(0);
            checker.onlineCertPath = onlineCertPath;
            final File f = new File(checker.onlineCertPath.toString());
            f.deleteOnExit();
            active = CetaCPFChecker.CETA_AVAILABLE;
            if (!active) {
                CPFOnlineChecker.log.log(Level.WARNING, "could not enable online certification due to problem when executing \"ceta\"");
            }
        return active ? checker : null;
    }

    @Override
    public String toString() {
        return "<!--\nNrProofSteps, "
               + this.certNrProofSteps
               + ", "
               + "Accepted, "
               + this.certAccepted
               + ", "
               + "Rejected, "
               + this.certRejected
               + ", "
               + "Unsupported, "
               + this.certUnsupported
               + ", "
               + "UnknownProofStructure, "
               + this.certUnknownProofStructure
               + ", "
               + "UnsupportedAprove, "
               + this.certUnsupportedAprove
               + ", "
               + "ProblemExport, "
               + this.certProblemExport
               + ", "
               + "ProblemExecCertifier, "
               + this.certProblemExecCertifier
               + "\n-->";
    }

    public void printStatistic() {
        System.out.println(this.toString());
    }

}
