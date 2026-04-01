package aprove.verification.diophantine;

import java.io.*;
import java.math.*;

import aprove.cli.Generic.*;


/**
 * A class to contain information on how a problem should be solved
 *
 * Note that this implementation is _not_ thread-safe. When you call a set* method, you must
 * be the only thread knowing about your particular instance, other threads can only safely access
 * this if they are started after the set* method[s] completed.
 *
 * @author bearperson
 * @version $Id$
 */
public class DioOptions extends CommandLineOptions {

    private static enum DioProblemType {
        DIOCONSTRAINTS, DIOLOGIC
    }

    public static enum DioOutputMode {
        SMTLIB("unknown", "sat", "unknown"),
        WST("TIMEOUT", "YES", "MAYBE");

        public final String TIMEOUT;
        public final String YES;
        public final String MAYBE;

        private DioOutputMode(String TIMEOUT, String YES, String MAYBE) {
            this.TIMEOUT = TIMEOUT;
            this.YES = YES;
            this.MAYBE = MAYBE;
        }
    }

    private String stratString = "";                    // -e Engine=MINISAT
    private BigInteger range = BigInteger.ONE;                              // -r 4
    private DioProblemType type = DioProblemType.DIOCONSTRAINTS;     // -d dioconstraints

    private DioOutputMode outputMode = DioOutputMode.WST;

    public DioOptions() {
        super();
    }

    public String getStrategyString() {
        return this.stratString;
    }

    public BigInteger getRange() {
        return this.range;
    }

    public DioOutputMode getOutputMode() {
        return this.outputMode;
    }

    @Override
    protected void setOne(final char opt, final String value) {
        switch(opt) {
        case 'e':
            this.stratString = "[" + value + "]";
            break;
        case 'r':
            this.range = BigInteger.valueOf(Long.parseLong(value));
            if (this.range.signum() <= 0) {
                throw new IllegalArgumentException("Invalid range " + this.range + ", valid values are > 0.");
            }
            break;
        case 'd':
            try {
                this.type = DioProblemType.valueOf(value.toUpperCase());
            } catch (final IllegalArgumentException noSuchValue) {
                // Make the message look a little nicer for the user
                throw new IllegalArgumentException("Error: type " + value + " not supported (yet?); aborting");
            }
            break;
        case 'm':
            this.outputMode = DioOutputMode.valueOf(value.toUpperCase());
            break;
        case 'u':
            break; // Has already been set, otherwise would not be here.

        default:
            super.setOne(opt, value);
        }
    }

    @Override
    protected String getAppName() {
        return "AProVE Diophantine Solver";
    }

    @Override
    protected String getOptsSpec() {
        return super.getOptsSpec() + "u:e:r:d:m:"; // u is for compatibility with the -u dio callings.
    }

    @Override
    protected void printHelp() {
        super.printHelp();
        // char count:      12345678901234567890123456789012345678901234567890123456789012345678901234567890
        System.out.println("Dio-specific options:");
        System.out.println("  -e Engine=MINISAT           Specify internal parameters to use");
        System.out.println("  -r <number>                 Range over which to search for solutions");
        System.out.println("  -d dioconstraints|diologic  Type of problem");
    }

    @Override
    public ProblemExecutor getExecutor(final Reader problemReader) {
        switch(this.type) {
        case DIOCONSTRAINTS:
            return new DioconstraintExecutor(problemReader, this);
        case DIOLOGIC:
            return new DiologicExecutor(problemReader, this);
        default:
            return null;
        }
    }
}
