package aprove.verification.oldframework.PropositionalLogic.SATCheckers;

import java.io.*;
import java.util.*;

/**
 * Dedicated parser for the SAT Race output format based on a state machine.
 *
 * See http://www.satcompetition.org/2009/format-solvers2009.html
 */
public class SATRaceParser {

    enum State {
        START,
        COMMENT,
        SOLUTION,
        VALUES,
        VAR,
        SKIP_VAR
    }

    /**
     * Parses a stream in the SAT Race output format
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

        /** Indicated the solver, that the formula is satisfiable?*/
        boolean satisfiable = false;

        State state = State.START;
        c = dataStream.read();

        int varNum = 0;

        while (c != -1) {

            switch(state) {
                case START:
                    if (SATRaceParser.isNewline(c) || SATRaceParser.isLinespace(c)) {
                        // ignore
                    } else if (c == 'c') {
                        state = State.COMMENT;
                    } else if (c == 's') {
                        state = State.SOLUTION;
                    } else if (c == 'v') {
                        state = State.VALUES;
                    } else {
                        return null;
                    }
                    break;

                case COMMENT:
                    if (SATRaceParser.isNewline(c)) {
                        state = State.START;
                    } else {
                        // ignore
                    }
                    break;

                case SOLUTION:
                    if (SATRaceParser.isNewline(c)) {
                        if (!satisfiable) {
                            return null;
                        }
                        state = State.START;
                    } else if (SATRaceParser.isLinespace(c)) {
                        // ignore
                    } else if (c == 'S') {
                        byte[] d = new byte[10];
                        int t = dataStream.read(d);
                        if (t < 10 || d[0] != 'A' || d[1] != 'T' || d[2] != 'I'
                                || d[3] != 'S' || d[4] != 'F' || d[5] != 'I'
                                || d[6] != 'A' || d[7] != 'B' || d[8] != 'L'
                                || d[9] != 'E') {
                            return null;
                        }
                        satisfiable = true;
                    } else {
                        // FIXME distinguish UNSAT and ERROR, there are applications
                        // where UNSAT actually means something
                        return null; // unsatisfiable or error or so
                    }
                    break;

                case VALUES:
                    if (SATRaceParser.isLinespace(c)) {
                        // ignore
                    } else if (SATRaceParser.isNewline(c)) {
                        state = State.START;
                    } else if (c == '0') {
                        return result;
                    } else if (c == '-') {
                        state = State.SKIP_VAR;
                    } else if (SATRaceParser.isDigit(c)) {
                        state = State.VAR;
                        varNum = SATRaceParser.toDigit(c);
                    } else {
                        return null; // invalid syntax;
                    }
                    break;

                case SKIP_VAR:
                    if (SATRaceParser.isNewline(c)) {
                        state = State.START;
                    } else if (SATRaceParser.isLinespace(c)) {
                        state = State.VALUES;
                    }
                    break;

                case VAR:
                    if (SATRaceParser.isDigit(c)) {
                        varNum = varNum*10 + SATRaceParser.toDigit(c);
                    } else if (SATRaceParser.isNewline(c)) {
                        if (!ignoreOther || c <= numVars) {
                            result.set(varNum);
                        }
                        state = State.START;
                    } else if (SATRaceParser.isLinespace(c)) {
                        if (!ignoreOther || c <= numVars) {
                            result.set(varNum);
                        }
                        state = State.VALUES;
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

    private static boolean isNewline(int b) {
        return b == '\n' || b == '\r';
    }

    private static boolean isLinespace(int b) {
        return b == ' ' || b == '\t';
    }

    private static int toDigit(int c) {
        return c - '0';
    }

    public static void main(String[] args) throws Exception {
        InputStream input = new FileInputStream(args[0]);
        BitSet bs = SATRaceParser.parseOutput(input, 0, false);
        System.out.println(bs);
    }

}
