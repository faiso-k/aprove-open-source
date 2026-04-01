package aprove.cli.Generic;

import java.io.*;

/**
 * Helper class for parsing problem inputs
 *
 * @author Karsten Behrmann
 * @version $Id$
 */
public abstract class InputUtil {

    private static final int MILLIS_BETWEEN_READS_AT_EOF = 1;
    // set to 5 for reproducing the state of July 07
    // set to 2 for good performance
    // set to 1 for state given to ManhThang Nguyen on 2007-12-08

    /**
     * basically reader.read(), except that EOF is handled specially.
     *
     * If ignoreEOF is true, EOF means a retry after a delay;
     * if false (or this thread gets interrupted during/before the delay) throws EOFException.
     */
    private static char getChar(Reader reader, boolean ignoreEOF) throws IOException {
        int ch = reader.read();
        while(ch == -1) {
            if (ignoreEOF) {
                // Wait and retry
                try {
                    Thread.sleep(InputUtil.MILLIS_BETWEEN_READS_AT_EOF);
                    ch = reader.read();
                    continue;
                } catch (InterruptedException fallthrough) {
                    // NOP
                }
            }
            // IgnoreEOF false or sleep got interrupted
            throw new EOFException("Unexpected EOF, expecting # to terminate problem");
        }
        // Okay, we got a good char, return it.
        return (char) ch;
    }

    /**
     * Fetches input until a # is encountered. Leading lines prefixed by %% are parsed as options.
     *
     * In our current input system, problems are seperated/terminated by # chars. So we
     * read until we find one. This function is guaranteed to not consume input past the # char
     * (though a BufferedReader may have read more and buffered it).
     * As an addition, any leading lines starting with %% are not made part of the problem,
     * but are parsed in a command-line-option style and merged into opts.
     * If the usual BufferedReader is used, this function is guaranteed to not block if the entire
     * problem can be read without blocking (that is, it won't block waiting for input beyond '#')
     *
     * @param reader The stream to read from
     * @param opts The options to merge inline options into (will be modified!)
     * @param ignoreEOF If true, this function will quietly keep retrying at EOF (handy for fifos)
     * @return a String containing the problem, as read from the input.
     * @throws IOException If the inputReader throws an exception
     * @throws EOFException If EOF is encountered unexpectedly before a # is read
     */
    public static String readProblem(BufferedReader reader, CommandLineOptions opts, boolean ignoreEOF) throws IOException, EOFException {
        StringBuilder buf = new StringBuilder();
        char ch;
        // NOTE: in the option parser, only one option per line is currently supported.
        while(true) {
            ch = InputUtil.getChar(reader, ignoreEOF);
            // Skip leading blanks and blank lines, for compatibility
            if (Character.isWhitespace(ch)) {
                continue;
            }
            // Check for double %. If not found, treat it as regular input and pass control to the next loop.
            if (ch != '%') {
                break;
            }
            ch = InputUtil.getChar(reader, ignoreEOF);
            if (ch != '%') {
                // This is the '%' from the first read. The second char could be a '#', loop below will catch that.
                buf.append('%');
                break;
            }

            // Okay, we have something that looks like an option.
            String optionSpec = reader.readLine();
            // Allow "%%@comment" so people can comment their option specs, if neccessary
            if (optionSpec.charAt(0) == '@') {
                continue;
            }
            // It really is an option. Process it.
            opts.setFromLine(optionSpec);
        }
        while(ch != '#') {
            buf.append(ch);
            ch = InputUtil.getChar(reader, ignoreEOF);
        }
        return buf.toString();
    }

}
