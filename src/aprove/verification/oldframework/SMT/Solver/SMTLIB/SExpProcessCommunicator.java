package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import java.io.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;
import immutables.*;

public class SExpProcessCommunicator {

    private static final Logger log = Logger.getLogger(SExpProcessCommunicator.class.toString());
    private final SExpList exit = new SExpList(new SExpSymbol("exit"));
    private boolean expectSuccess = true;
    private final SExpStreamParser p;
    private final InputStreamReader i;
    private final OutputStreamWriter o;
    private final Process proc;
    private final SExpAtom success = new SExpSymbol("success");
    private final Abortion abortion;

    public SExpProcessCommunicator(Abortion abortion, String... cmd) throws IOException {
        ProcessBuilder pb = new ProcessBuilder(cmd);
        this.expectSuccess = true;
        Process p = pb.start();
        this.proc = p;
        this.abortion = abortion;
        TrackerFactory.process(abortion, this.proc);
        this.o = new OutputStreamWriter(new BufferedOutputStream(p.getOutputStream()));
        this.i = new InputStreamReader(new BufferedInputStream(p.getInputStream()));
        this.p = new SExpStreamParser(this.i);
    }

    protected SExpProcessCommunicator(Abortion aborter) {
        this.expectSuccess = true;
        this.proc = null;
        this.abortion = aborter;
        this.o = null;
        this.i = null;
        this.p = null;
    }

    public SExp command(SExp s) throws IOException, ParserException, AbortionException {
        this.send(s);
        SExp rv = this.receive();
        if (rv instanceof SExpList) {
            SExpList l = (SExpList) rv;
            ImmutableList<SExp> a = l.getArgs();
            if (a.size() == 2 && a.get(0).equals(new SExpSymbol("error"))) {
                throw new RuntimeException("SMTLIB error: " + a.get(1).toString());
            }
        }
        return rv;
    }

    public void exit() {
        try {
            this.send(this.exit);
            this.proc.waitFor();
        } catch (IOException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    public boolean isExpectSuccess() {
        return this.expectSuccess;
    }

    private SExp receive() throws ParserException, IOException {
        this.abortion.checkAbortion();
        SExp rv = this.p.parse();
        if (SExpProcessCommunicator.log.isLoggable(Level.FINE)) {
            SExpProcessCommunicator.log.fine("SMT recv: " + rv);
        }
        return rv;
    }

    private void send(SExp s) throws IOException, AbortionException {
        this.abortion.checkAbortion();
        try {
            if (SExpProcessCommunicator.log.isLoggable(Level.FINE)) {
                SExpProcessCommunicator.log.fine("SMT send: " + s);
            }
            s.appendTo(this.o);
            this.o.append('\n');
            this.o.flush();
        } finally {
            this.abortion.checkAbortion();
        }
    }

    public void setExpectSuccess(boolean expectSuccess) {
        this.expectSuccess = expectSuccess;
    }

    public void successCommand(SExp s) throws IOException, ParserException, AbortionException {
        if (this.expectSuccess) {
            SExp rv = this.command(s);
            if (!this.success.equals(rv)) {
                throw new RuntimeException("Expected success, got: " + rv);
            }
        } else {
            this.send(s);
        }
    }

    public void dispose() throws IOException {
        this.proc.destroy();
        this.o.close();
        this.i.close();
    }

}
