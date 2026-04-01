package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import java.io.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;

/**
 * Adds a FileWriter to the process communicator and redirects all commands to that writer instead of executing the
 * commands.
 * @author cryingshadow
 * @version $Id$
 */
public class SExpDumpCommunicator extends SExpProcessCommunicator {

    /**
     * Writer to dump the queries to.
     */
    private final FileWriter writer;

    /**
     * @param w Writer to dump the queries to.
     * @param abortion Aborter.
     * @param cmd Command for the process (still needed since the process is started anyway).
     * @throws IOException If some I/O error occurs.
     */
    public SExpDumpCommunicator(FileWriter w, Abortion abortion) throws IOException {
        super(abortion);
        this.writer = w;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.SMT.Solver.SMTLIB.SExpProcessCommunicator#command(aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.SExp)
     */
    @Override
    public SExp command(SExp s) throws IOException, ParserException, AbortionException {
        this.send(s);
        return new SExpSymbol("success");
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.SMT.Solver.SMTLIB.SExpProcessCommunicator#successCommand(aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.SExp)
     */
    @Override
    public void successCommand(SExp s) throws IOException, ParserException, AbortionException {
        this.send(s);
    }

    /**
     * Dumps the specified expression to the writer.
     * @param s An expression.
     * @throws IOException If some I/O error occurs.
     */
    private void send(SExp s) throws IOException {
        this.writer.write(s.toString());
        this.writer.write('\n');
    }

}
