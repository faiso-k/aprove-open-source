package aprove.input.Programs.Strategy;

import java.io.*;

import org.antlr.runtime.*;

import aprove.input.Generated.Strategy.*;
import aprove.exit.*;

public class PrettyPrinterMain {

    /**
     * Read a strategy file and print it pretty.
     */
    public static void main(final String[] args) {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(final String[] args) throws KillAproveException {
        StrategyLexer sl;
        try {
            sl = new StrategyLexer(new ANTLRFileStream(args[0]));
            CommonTokenStream tokens = new CommonTokenStream(sl);
            final StrategyParser sp = new StrategyParser(tokens);

            final RawModule rm = sp.strategy();

            final PrettyPrinter pp = new PrettyPrinter();
            rm.accept(pp);
            final String pretty = pp.getContents();

            try (final FileWriter fw = new FileWriter("/tmp/blafasel")) {
                fw.write(pretty);
            }
            System.out.print(pretty);
            throw new KillAproveException(1);
        } catch (final IOException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        } catch (final RecognitionException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
}
