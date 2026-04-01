package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;

/*
 * Dedicated parser for the MiniSAT output format based on a state machine
 */
public class MiniSATParser {

    enum State {
        SAT,
        VAR,
        SKIP_VAR,
    }

    /**
     * Parses a stream in the MiniSAT2 output format
     *
     * Returns a BitSet with a valid model where All DONT-CAREs are set to zero.
     *
     * @param numVars
     *            Number of variables in the output stream. Used for
     *            initializing the bitset.
     * @param ignoreOther
     *            If true, variables with number > numVars are completely
     *            ignored.
     */
    public static BitSet parseOutput(InputStream dataStream, int numVars, boolean ignoreOther) throws IOException {
        BitSet result = new BitSet(numVars + 1);
        int c;

        {
            byte data[] = new byte[4];
            c = dataStream.read(data);
            if (c < 4 || !(     data[0] == 'S' && data[1] == 'A' && data[2] == 'T' && MiniSATParser.isSpace(data[3]))) {
                // FIXME distinguish UNSAT and ERROR, there are applications
                // where UNSAT actually means something
                return null; // Unsatisfiable (or error or so)
            }
        }

        State state = State.SAT;
        int varNum = 0;
        c = dataStream.read();

        while (c != -1) {

            switch(state) {
                case SAT:
                    if (MiniSATParser.isSpace(c)) {
                        // ignore
                    } else if (c == '0') {
                        return result;
                    } else if (c == '-') {
                        state = State.SKIP_VAR;
                    } else if (MiniSATParser.isDigit(c)) {
                        state = State.VAR;
                        varNum = MiniSATParser.toDigit(c);
                    }
                    break;

                case SKIP_VAR:
                    if (MiniSATParser.isSpace(c)) {
                        state = State.SAT;
                    }
                    break;

                case VAR:
                    if (MiniSATParser.isDigit(c)) {
                        varNum = varNum*10 + MiniSATParser.toDigit(c);
                    } else if (MiniSATParser.isSpace(c)) {
                        if (!ignoreOther || c <= numVars) {
                            result.set(varNum);
                        }
                        state = State.SAT;
                    } else {
                        return null;
                    }
                    break;
            }

            c = dataStream.read();
        }

        return null;
    }

    private static boolean isDigit(int c) {
        return c >= '0' && c <= '9';
    }

    private static boolean isSpace(int b) {
        return b == '\n' || b == '\r' || b == ' ' || b == '\t';
    }

    private static int toDigit(int c) {
        return c - '0';
    }

}
