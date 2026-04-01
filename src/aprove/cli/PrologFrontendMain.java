package aprove.cli;

import gnu.getopt.*;

import java.util.*;

import aprove.exit.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class PrologFrontendMain extends FrontendMain<PrologFrontendMain.PrologFrontendOpts> {
    /**
     * Record-like class holding all options for this frontend.
     */
    static class PrologFrontendOpts extends FrontendMain.FrontendOpts {
        /** JSON Graph export. */
        boolean jsonExport = false;

        /** Start term. */
        String startTerm = null;
    }

    @Override
    PrologFrontendOpts createFrontendOpts() {
        return new PrologFrontendOpts();
    }

    @Override
    Getopt createGetopt(List<LongOpt> longoptsArg, String[] argv) {
        List<LongOpt> longopts = new LinkedList<>(longoptsArg);
        longopts.add(new LongOpt("startTerm", LongOpt.REQUIRED_ARGUMENT, null, 's'));
        return new Getopt("AProVE Prolog Frontend", argv, "ho:t:ps:g:j:", longopts.toArray(new LongOpt[0]));
    }

    @Override
    String getExtension() {
        return "pl";
    }

    @Override
    String getStrategyName() {
        if (this.options.graphExport) {
            return "aprove.FrontendExport.PrologFrontend-graph";
        } else if (this.options.jsonExport) {
            return "aprove.FrontendExport.PrologFrontend-json";
        } else {
            return "aprove.FrontendExport.PrologFrontend-trs";
        }
    }

    @Override
    void parseAdditionalCommandLineOption(Getopt g, int c) throws KillAproveException {
        switch (c) {
        case 's':
            final String startTerm = g.getOptarg();
            this.options.startTerm = startTerm;
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
        default:
            this.printHelp();
            throw new KillAproveException(1);
        }
    }

    @Override
    void printCmdOptionsInfo() {
        super.printCmdOptionsInfo();
        System.out.println(" -s, --startTerm TERM   analyze termination starting with term TERM");
        System.out.println(" -j, --json yes|no      export JSON (default no), conflicts with other output");
    }

    @Override
    void printHelp() {
        System.out.println("Usage: java -cp aprove.jar aprove.CommandLineInterface.PrologFrontendMain [OPTION] PLFILE\n");
        System.out.println("Prolog to QDP/Graph dump export from AProVE 2014.");
        System.out.println();
        this.printCmdOptionsInfo();
    }

    @Override
    Pair<String, Input> init(String[] args) throws KillAproveException {
        Pair<String, Input> res = super.init(args);
        if (this.options.startTerm != null) {
            res.y.setProtoAnnotation(this.options.startTerm);
        }
        return res;
    }

    public static void main(String args[]) {
        try {
            new PrologFrontendMain().run(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }
}
