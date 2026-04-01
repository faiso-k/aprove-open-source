package aprove.cli.Generic;

import java.io.*;

/**
 * This class aborts the given executor when triggered to do so by the given stream
 *
 * Specifically, reading a 'q' char will abort the executor. Any exception raised by
 * read() will also do so, so on sockets, conn.setSoTimeout() can be used as a crude
 * timeout mechanism.
 *
 * @author Karsten Behrmann
 * @version $Id$
 */
class SocketAborterThread extends Thread {
    private ProblemExecutor executor;
    private Reader commandReader;

    public SocketAborterThread(ProblemExecutor executor, Reader commandReader) {
        super("socket aborter thread");
        this.executor = executor;
        this.commandReader = commandReader;
    }

    @Override
    public void run() {
        while(true) {
            try {
                int ch = this.commandReader.read();
                if (ch == -1 || ch == 'q') {
                    break;
                }
            } catch (IOException interruptedOrError) {
                break;
            }
        }
        this.executor.abort();
    }
}
