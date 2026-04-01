package aprove.solver.Engines;

import java.io.*;
import java.util.*;
import java.util.Map.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author cotto
 */
public class ExecHelper {

    /**
     * @param string
     * @param aborter
     * @return
     * @throws IOException
     * @throws InterruptedException
     */
    public static Pair<List<String>, List<String>> exec(final List<String> cmds, final Abortion aborter)
            throws IOException, InterruptedException {
        Triple<Integer, List<String>, List<String>> res = execAndGetExitCode(cmds, Collections.emptyMap(), aborter);
        return new Pair<List<String>, List<String>>(res.y, res.z);
    }

    /**
     * @param cmds
     * @param aborter
     * @return
     * @throws IOException
     * @throws InterruptedException
     */
    public static Triple<Integer, List<String>, List<String>> execAndGetExitCode(final List<String> cmds, Map<String, String> addToEnv, final Abortion aborter)
            throws IOException, InterruptedException {
        ProcessBuilder pb = new ProcessBuilder(cmds);
        Map<String, String> pbEnv = pb.environment();
        for (Entry<String, String> e: addToEnv.entrySet()) {
            pbEnv.put(e.getKey(), e.getValue());
        }
        Process process = pb.start();

        final BufferedStreamInThread inputStream = new BufferedStreamInThread(process.getInputStream());
        final BufferedStreamInThread errorStream = new BufferedStreamInThread(process.getErrorStream());

        TrackerFactory.process(aborter, process);

        int exitCode = process.waitFor();

        final Triple<Integer, List<String>, List<String>> res =
            new Triple<>(exitCode, inputStream.getLines(), errorStream.getLines());

        process.getErrorStream().close();
        process.getInputStream().close();
        process.destroy();

        return res;
    }

}

class BufferedStreamInThread extends Thread {
    InputStream is;
    private List<String> lines;

    BufferedStreamInThread(final InputStream is) {
        this.is = is;
        this.start();
    }

    /**
     * @return
     */
    public List<String> getLines() {
        while (true) {
            synchronized (this) {
                if (this.lines == null) {
                    try {
                        this.wait();
                    } catch (final InterruptedException e) {
                        return null;
                    }
                } else {
                    break;
                }
            }
        }
        return this.lines;
    }

    @Override
    public void run() {
        final BufferedInputStream bufferedReader = new BufferedInputStream(this.is);
        final Scanner scanner = new Scanner(bufferedReader);
        final List<String> linesTemp = new LinkedList<String>();
        while (scanner.hasNextLine()) {
            final String line = scanner.nextLine();
            linesTemp.add(line);
        }
        scanner.close();
        synchronized (this) {
            this.lines = linesTemp;
            this.notify();
        }
    }
}