package aprove.cli.Generic;

import gnu.getopt.*;

import java.io.*;
import java.util.regex.*;

/**
 * Base class implementing command line options and how to solve a problem.
 *
 * Implement getExecutor to declare how problems should be handled.
 * Note that if you need fields containing mutable types, you will want to override
 * the clone() method in your subclass, or server mode will behave weird.
 *
 * @author Karsten Behrmann
 * @version $Id$
 */
public abstract class CommandLineOptions implements Cloneable {

    private static final Pattern OPTLINE_REGEX = Pattern.compile("-?(.)(?: (.*))?");

    private boolean printTimeSpent = false;               // -p
    private boolean verbose = false;                      // -v
    private boolean synchroneous = false;                 // -s
    private long timeLimit = 0;                           // -t 4711
    private String inputFileNameForInteractive = null;    // -i /tmp/somefifo
    private String outputFileNameForInteractive = null;   // -o /tmp/otherfifo
    private Integer port = null;                          // -l 5123

    public CommandLineOptions() {
    }

    @Override
    public CommandLineOptions clone() {
        try {
            return (CommandLineOptions) super.clone();
        } catch (CloneNotSupportedException whatAreYouSmoking) {
            // Screw you, java. If this happens, you blatantly ignored my implementing Cloneable.
            throw new RuntimeException(whatAreYouSmoking);
        }
    }

    /** Should we return our idea of how much time we spent?
     */
    public boolean getPrintTimeSpent() {
        return this.printTimeSpent;
    }

    public boolean isVerbose() {
        return this.verbose;
    }

    /** Should we refuse to process a new problem until all outstanding ones are finished?
     */
    public boolean isSynchroneous() {
        return this.synchroneous;
    }

    /** After how much time should we abort? (in milliseconds)
     */
    public long getTimeLimit() {
        return this.timeLimit;
    }

    public boolean hasTimeLimit() {
        return (this.timeLimit != 0);
    }

    public String getInputFileNameForInteractive() {
        return this.inputFileNameForInteractive;
    }

    public String getOutputFileNameForInteractive() {
        return this.outputFileNameForInteractive;
    }

    public boolean hasPort() {
        return (this.port != null);
    }

    public int getPort() {
        return this.port.intValue();
    }

    protected void setOne(char opt, String value) {
        switch(opt) {
        case 'h':
            this.printHelp();
            throw new IllegalArgumentException("Help requested, quitting.");
        case 'p':
            this.printTimeSpent = ! this.printTimeSpent;
            break;
        case 'v':
            this.verbose = ! this.verbose;
            break;
        case 's':
            this.synchroneous = ! this.synchroneous;
            break;
        case 't':
            this.timeLimit = Long.parseLong(value) * 1000;
            if (this.timeLimit < 0) {
                throw new IllegalArgumentException("Invalid time limit " + this.timeLimit +
                ", valid values are >= 0 (0 for no timeout).");
            }
            break;
        case 'i':
            this.inputFileNameForInteractive = value;
            break;
        case 'o':
            this.outputFileNameForInteractive = value;
            break;
        case 'l':
            this.port = Integer.valueOf(value);
            break;
        default:
            throw new IllegalArgumentException("Unrecognized option '-" + opt + "'!");
        }
    }

    // Overridden in subclass
    protected String getAppName() {
        return "AProVE unnamed CLI";
    }

    // Overridden in subclass
    protected String getOptsSpec() {
        return "hpvst:i:o:l:";
    }

    public int setFromCommandLine(String[] args) {
        // I hope we don't need more long options anytime soon, the interface sucks.
        LongOpt[] longOpts = new LongOpt[1];
        longOpts[0] = new LongOpt("help", LongOpt.NO_ARGUMENT, null, 'h');

        Getopt g = new Getopt(this.getAppName(), args, this.getOptsSpec(), longOpts);
        int c;
        while ((c = g.getopt()) != -1) {
            // TODO: catch error/special returns from getopt()
            this.setOne((char)c, g.getOptarg());
        }

        // Return the first non-option index
        return g.getOptind();
    }

    public void setFromLine(String optionSpec) {
        Matcher parsedOpt = CommandLineOptions.OPTLINE_REGEX.matcher(optionSpec);
        if (!parsedOpt.matches()) {
            throw new IllegalArgumentException ("Bad option line '" + optionSpec + "', " +
                                                "note that only one option per line is currently supported.");
        }
        // Simplified, the regex is "-(.) (.*)"
        this.setOne(parsedOpt.group(1).charAt(0), parsedOpt.group(2));
    }

    protected void printHelp() {
        System.out.println(this.getAppName() + " command line options");
        // char count:      12345678901234567890123456789012345678901234567890123456789012345678901234567890
        System.out.println("All options can be specified for a specific problem by prefixing the problem");
        System.out.println("with lines starting with a double % mark (e.g. \"%%-t 10000\"). Comments can");
        System.out.println("be added there as \"%%@commentline\".");
        System.out.println("For regular mode, pass a problem file name on the command line.");
        System.out.println("For interactive mode, pass a '-' character. For server mode, specify -l.");
        System.out.println("Available general options:");
        System.out.println("  -h / --help   this screen.");
        System.out.println("  -p            print time spent");
        System.out.println("  -v            be verbose");
        System.out.println("  -s            refuse to start if a problem is still processing (sync mode)");
        System.out.println("  -t <number>   time limit in seconds");
        System.out.println("  -i somefifo   input file for interactive mode");
        System.out.println("  -o otherfifo  output file for interactive mode");
        System.out.println("  -l port       port to listen on, enables TCP server mode");
    }

    public abstract ProblemExecutor getExecutor(Reader problemReader);

}