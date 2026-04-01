package aprove.cli;

import java.util.*;

import aprove.exit.*;
import gnu.getopt.*;

public class JBCFrontendMain extends FrontendMain<JBCFrontendMain.JBCFrontendOpts> {
    /**
     * Record-like class holding all options for this frontend.
     */
    static class JBCFrontendOpts extends aprove.cli.FrontendMain.FrontendOpts {
        /** JSON Graph export. */
        boolean jsonExport = false;

        /** Simplify the resulting systems. */
        boolean simplify = true;

        /** Try to export to QDP if possible. */
        boolean tryQDPExport = true;

        /** Export into the T2 integer transition format. */
        boolean t2Export = false;

        /** Export into the HSF clauses format. */
        boolean clausesExport = false;

        /** Export into the SMTLIB Pushdown automaton format. */
        boolean pushdownExport = false;
    }

    @Override
    JBCFrontendOpts createFrontendOpts() {
        return new JBCFrontendOpts();
    }

    @Override
    Getopt createGetopt(final List<LongOpt> longoptsArg, final String[] argv) {
        final List<LongOpt> longopts = new LinkedList<>(longoptsArg);
        longopts.add(new LongOpt("simplify", LongOpt.REQUIRED_ARGUMENT, null, 's'));
        longopts.add(new LongOpt("qdpExport", LongOpt.REQUIRED_ARGUMENT, null, 'Q'));
        longopts.add(new LongOpt("t2", LongOpt.REQUIRED_ARGUMENT, null, '2'));
        longopts.add(new LongOpt("clauses", LongOpt.REQUIRED_ARGUMENT, null, 'c'));
        longopts.add(new LongOpt("pushdown", LongOpt.REQUIRED_ARGUMENT, null, 'a'));
        longopts.add(new LongOpt("json", LongOpt.REQUIRED_ARGUMENT, null, 'j'));
        return new Getopt("AProVE JBC Frontend", argv, "hs:q:Q:o:t:2:c:g:a:j:", longopts.toArray(new LongOpt[0]));
    }

    @Override
    String getExtension() {
        return "jar";
    }

    @Override
    String getStrategyName() {
        final String exportType;
        if (this.options.graphExport){
            exportType = "graph";
        } else if (this.options.jsonExport) {
            exportType = "json";
        } else if (this.options.t2Export) {
            exportType = "toT2";
        } else if (this.options.clausesExport) {
            exportType = "toClauses";
        } else if (this.options.pushdownExport) {
            exportType = "toPushdown";
        } else if (this.options.tryQDPExport) {
            exportType = "withQDP";
        } else {
            exportType = "noQDP";
        }
        String simplifyType = null;
        if (!this.options.graphExport && !this.options.jsonExport) {
            if (this.options.simplify) {
                simplifyType = "withSimplify";
            } else {
                simplifyType = "noSimplify";
            }
        }
        return "aprove.FrontendExport.JBCFrontend-"
                + exportType
                + (simplifyType == null ? "" : "-" + simplifyType);
    }

    @Override
    void parseAdditionalCommandLineOption(final Getopt g, final int c) throws KillAproveException {
        switch (c) {
            case 'Q':
                final String tryQDP = g.getOptarg();
                if (FrontendMain.isTrueString(tryQDP)) {
                    this.options.tryQDPExport = true;
                } else if (FrontendMain.isFalseString(tryQDP)) {
                    this.options.tryQDPExport = false;
                } else {
                    System.err.println("Failed to parse tryQDP option '" + tryQDP + "', using default 'true'.");
                }
                break;
            case 's':
                final String simplify = g.getOptarg();
                if (FrontendMain.isTrueString(simplify)) {
                    this.options.simplify = true;
                } else if (FrontendMain.isFalseString(simplify)) {
                    this.options.simplify = false;
                } else {
                    System.err.println("Failed to parse simplify option '" + simplify + "', using default 'true'.");
                }
                break;
            case '2':
                final String t2Export = g.getOptarg();
                if (FrontendMain.isTrueString(t2Export)) {
                    this.options.t2Export = true;
                } else if (FrontendMain.isFalseString(t2Export)) {
                    this.options.t2Export = false;
                } else {
                    System.err.println("Failed to parse t2 option '" + t2Export + "', using default 'false'.");
                }
                break;
            case 'c':
                final String clausesExport = g.getOptarg();
                if (FrontendMain.isTrueString(clausesExport)) {
                    this.options.clausesExport = true;
                } else if (FrontendMain.isFalseString(clausesExport)) {
                    this.options.clausesExport = false;
                } else {
                    System.err.println("Failed to parse clauses option '" + clausesExport + "', using default 'false'.");
                }
                break;
            case 'a':
                final String pushdownExport = g.getOptarg();
                if (FrontendMain.isTrueString(pushdownExport)) {
                    this.options.pushdownExport = true;
                } else if (FrontendMain.isFalseString(pushdownExport)) {
                    this.options.pushdownExport = false;
                } else {
                    System.err.println("Failed to parse pushdown option '" + pushdownExport + "', using default 'false'.");
                }
                break;
            case 'j':
                final String json = g.getOptarg();
                if (FrontendMain.isTrueString(json)) {
                    this.options.jsonExport = true;
                } else if (FrontendMain.isFalseString(json)) {
                    this.options.jsonExport = false;
                } else {
                    System.err.println("Failed to parse JSON export option '" + json + "', using default 'false'.");
                }
                break;
            case 'h':
            default:
                this.printHelp();
                throw new KillAproveException(1);
        }
    }

    @Override
    void printCmdOptionsInfo() {
        super.printCmdOptionsInfo();
        System.out.println(" -s, --simplify yes|no  simplify resulting TRSs (default yes)");
        System.out.println(" -Q, --qdp yes|no       if possible, produce a QDP (default yes), conflicts with other output");
        System.out.println(" -2, --t2 yes|no        export to T2 transition systems (default no), conflicts with other output");
        System.out.println(" -c, --clauses yes|no   export to HSF clauses (default no), conflicts with other output");
        System.out.println(" -a, --pushdown yes|no  export Pushdown automaton (default no), conflicts with other output");
        System.out.println(" -j, --json yes|no      export JSON (default no), conflicts with other output");
        System.out.println(" -J, --jar-file         path to a jar-file containing additional classes (e.g., rt.jar)");
    }

    @Override
    void printHelp() {
        System.out.println("Usage: java -cp aprove.jar aprove.CommandLineInterface.JBCFrontendMain [OPTION] JARFILE\n");
        System.out.println("JBC to intTRS/QDP/Termination Graph dump export from AProVE 2014.");
        System.out.println("");
        this.printCmdOptionsInfo();
    }

    @Override
    void checkOptionSanity(final Getopt g, final String[] args) throws KillAproveException {
        super.checkOptionSanity(g, args);
        if (this.options.t2Export && this.options.clausesExport) {
            System.err.println("Conflicting options --t2 and --clauses given, aborting.");
            this.printHelp();
            throw new KillAproveException(1);
        }

        if (this.options.t2Export && this.options.pushdownExport) {
            System.err.println("Conflicting options --t2 and --pushdown given, aborting.");
            this.printHelp();
            throw new KillAproveException(1);
        }

        if (this.options.clausesExport && this.options.pushdownExport) {
            System.err.println("Conflicting options --clauses and --pushdown given, aborting.");
            this.printHelp();
            throw new KillAproveException(1);
        }

        if (this.options.jsonExport && (this.options.clausesExport || this.options.t2Export || this.options.pushdownExport)) {
            System.err.println("Conflicting export options given, aborting.");
            this.printHelp();
            throw new KillAproveException(1);
        }
    }

    public static void main(final String args[]) {
        try {
            new JBCFrontendMain().run(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }
}
