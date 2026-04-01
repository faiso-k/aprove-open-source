package aprove.verification.oldframework.CPF;

import java.io.*;
import java.util.logging.*;

import aprove.api.prooftree.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class CetaCPFChecker {

    public static Logger log = java.util.logging.Logger.getLogger("CetaCPFChecker");

    public final static boolean CETA_AVAILABLE;

    static {
        boolean active = false;
        try {
            final Process p = Runtime.getRuntime().exec("ceta");
            active = (p.waitFor() == 4);
        } catch (final IOException e) {
        } catch (final InterruptedException e) {
        }
        CETA_AVAILABLE = active;
    }


    private static String getContentAndDelete(final File f) {
        try {
            final BufferedReader r = new BufferedReader(new FileReader(f));
            final StringBuilder b = new StringBuilder();
            while (r.ready()) {
                b.append(r.readLine());
                b.append("\n");
            }
            r.close();
            f.delete();
            return b.toString();
        } catch (final IOException e) {
            return "IOException occured while reading";
        }
    }

    /**
     * Checks whether a CPF can be certified by CeTA.
     * First writes the CPF to file, and then invokes an external process.
     * @param cpf
     * @param cpfFileName
     * @return a triple consisting of a result and two strings. The strings are null, if some problem
     *   occurred when running ceta, and otherwise they are stdout and stderr from ceta.
     */
    /*
     * TODO: one might want to support a timeout
     */
    public static Triple<CPFCheckResult,String,String> checkCPF(final CPF cpf, final String cpfFileName) {
        if (!CetaCPFChecker.CETA_AVAILABLE) {
            return new Triple<>(CPFCheckResult.CeTAnotAvailable, null, null);
        }
        final File f = new File(cpfFileName);
        boolean fileWritten = false;
        OutputStream ostream = null;
        try {
            ostream = new BufferedOutputStream(new FileOutputStream(f));
            cpf.writeCPF(ostream);
            ostream.flush();
            ostream.close();
            ostream = null;
            fileWritten = true;
        } catch (final Exception e) {
            CetaCPFChecker.log.log(Level.WARNING, "problem in generaring CPF",e);
            if (ostream != null) {
                try {
                    ostream.close();
                } catch (final IOException e2) {
                }
            }
        } finally {
            if (ostream != null) {
                try {
                    ostream.close();
                } catch (final IOException e) {
                }
            }
        }
        if (!fileWritten) {
            return new Triple<>(CPFCheckResult.ErrorWhenGeneratingCPF, null, null);
        }
        Process ceta = null;
        try {
            final ProcessBuilder pb =
                new ProcessBuilder("ceta", "--allow-assumptions", cpfFileName);
            String prefix = f.getName();
            // if the prefix is shorter than 3 characters, then createTempFile throws an exception
            while (prefix.length() < 3) {
                prefix = prefix + (int)Math.random();
            }
            final File cetaErr = File.createTempFile(prefix, ".ceta_error.txt");
            final File cetaOut = File.createTempFile(prefix, ".ceta_out.txt");
            pb.redirectError(cetaErr);
            pb.redirectOutput(cetaOut);
            ceta = pb.start();
            final int cetaReturn = ceta.waitFor();
            ceta.destroy();
            final String stdout = CetaCPFChecker.getContentAndDelete(cetaOut);
            final String stderr = CetaCPFChecker.getContentAndDelete(cetaErr);
            ceta = null;
            if (cetaReturn == 0) {
                return new Triple<>(CPFCheckResult.Certified, stdout, stderr);
            } else if (cetaReturn == 1) {
                CetaCPFChecker.log.log(Level.SEVERE, "CeTA rejected " + cpfFileName);
                return new Triple<>(CPFCheckResult.RejectedByCertifier, stdout, stderr);
            } else {
                return new Triple<>(CPFCheckResult.UnsupportedByCertifier, stdout, stderr);
            }
        } catch (final Exception e) {
            CetaCPFChecker.log.log(Level.WARNING, "problem in executing CeTA",e);
            if (ceta != null) {
                ceta.destroy();
            }
            return new Triple<>(CPFCheckResult.ErrorInvokingCertifier, null, null);
        }
    }
}
