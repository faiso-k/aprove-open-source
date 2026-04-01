package aprove.input.Programs.haskell;

import java.io.*;

import aprove.exit.*;

/**
 * replaces the private flag of the push method by public
 *
 * @author matraf
 */
public class HaskellParserModifier {

    private static final String searchPattern = "private void push";
    private static final String replacePattern = "public void push";

    /**
     * expects the filename of the parser to modify as first argument
     * the return value is 0 on success, 1 otherwise
     */
    public static void main(final String[] argv) {
        try {
            doMain(argv);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(final String[] argv) throws KillAproveException {
        if (argv.length < 1) {
            System.err.println("ERROR: No file specified!");
            throw new KillAproveException(1);
        }
        final String fileName = argv[0];
        File inputFile = new File(fileName);
        try {
            final String tmpFileName = inputFile.getCanonicalPath() + ".tmp";
            File tmpFile = new File(tmpFileName);
            while (tmpFile.exists()) {
                tmpFile = new File(tmpFile.getCanonicalPath() + ".tmp");
            }
            if (!inputFile.renameTo(tmpFile)) {
                throw new IOException("could not rename file to temporary file");
            }
            inputFile = tmpFile;
            inputFile.deleteOnExit();
        } catch (final Exception e) {
            try {
                System.err.println("ERROR: could not open file " + inputFile.getCanonicalPath() + " for reading.");
            } catch (final IOException ioE) {
                System.err.println("ERROR: can't even get the name of the inputFile");
                ioE.printStackTrace();
                System.err.println("ERROR: following is the stack trace that brought us here:");
            }
            e.printStackTrace();
            throw new KillAproveException(1);
        }
        try (BufferedReader reader = new BufferedReader(new InputStreamReader(new FileInputStream(inputFile)))) {
            final String newFileName = fileName;
            OutputStreamWriter osw = null;
            final File tempFile = new File(newFileName);
            try {
                osw = new OutputStreamWriter(new FileOutputStream(tempFile));
            } catch (final Exception e) {
                System.err.println("ERROR: could not open temporary file " + newFileName + " for writing");
                e.printStackTrace();
                throw new KillAproveException(1);
            }
            try {
                boolean found = false;
                while (reader.ready()) {
                    String line = reader.readLine();
                    if (!found) {
                        final String newLine = line.replaceFirst(HaskellParserModifier.searchPattern, HaskellParserModifier.replacePattern);
                        found = (!line.equals(newLine));
                        line = newLine;
                    }
                    osw.write(line + "\n");
                }
                osw.close();
            } catch (final IOException e) {
                System.err.println("ERROR: write to temporary file failed");
                e.printStackTrace();
                throw new KillAproveException(1);
            }
        } catch (KillAproveException e) {
            throw e;
        } catch (final Exception e) {
            try {
                System.err.println("ERROR: could not open file " + inputFile.getCanonicalPath() + " for reading.");
            } catch (final IOException ioE) {
                System.err.println("ERROR: can't even get the name of the inputFile");
                ioE.printStackTrace();
                System.err.println("ERROR: following is the stack trace that brought us here:");
            }
            e.printStackTrace();
            throw new KillAproveException(1);
        }
        throw new KillAproveException(0);
    }
}
