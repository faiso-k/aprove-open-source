package aprove.cli;

import gnu.getopt.*;

import java.util.*;

import aprove.exit.*;

public class LLVMFrontendMain extends FrontendMain<LLVMFrontendMain.LLVMFrontendOpts> {
    /**
     * Record-like class holding all options for this frontend.
     */
    static class LLVMFrontendOpts extends aprove.cli.FrontendMain.FrontendOpts {
        /** JSON Graph export. */
        boolean jsonExport = false;
    }

    @Override
    LLVMFrontendOpts createFrontendOpts() {
        return new LLVMFrontendOpts();
    }

    @Override
    Getopt createGetopt(final List<LongOpt> longoptsArg, final String[] argv) {
        final List<LongOpt> longopts = new LinkedList<>(longoptsArg);
        longopts.add(new LongOpt("simplify", LongOpt.REQUIRED_ARGUMENT, null, 's'));
        longopts.add(new LongOpt("json", LongOpt.REQUIRED_ARGUMENT, null, 'j'));
        return new Getopt("AProVE LLVM Frontend", argv, "hs:o:t:g:j:", longopts.toArray(new LongOpt[0]));
    }

    @Override
    String getExtension() {
        return "llvm";
    }

    @Override
    String getStrategyName() {
        if (this.options.graphExport) {
            return "aprove.FrontendExport.LLVMFrontend-graph";
        } else if (this.options.jsonExport) {
            return "aprove.FrontendExport.LLVMFrontend-json";
        } else {
            return "aprove.FrontendExport.LLVMFrontend-trs";
        }
    }

    @Override
    void parseAdditionalCommandLineOption(final Getopt g, final int c) throws KillAproveException {
        switch (c) {
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
        System.out.println(" -j, --json yes|no      export JSON (default no), conflicts with other output");
    }

    @Override
    void printHelp() {
        System.out.println("Usage: java -cp aprove.jar aprove.CommandLineInterface.LLVMFrontendMain [OPTION] LLVMFILE\n");
        System.out.println("");
        this.printCmdOptionsInfo();
    }

    @Override
    void checkOptionSanity(final Getopt g, final String[] args) throws KillAproveException {
        super.checkOptionSanity(g, args);
    }

    public static void main(final String args[]) {
        try {
            new LLVMFrontendMain().run(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }
}
