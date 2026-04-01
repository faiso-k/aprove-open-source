package aprove.strategies.Abortions;

import java.io.*;
import java.net.*;
import java.util.logging.*;

import aprove.*;

public class ExternalSpawner {
    private static Logger log = Logger.getLogger(ExternalSpawner.class.getName());
    private static int MINISATD_PORT;

    static {
        if (Globals.useExternalSpawner) {
            try {
                Runtime runtime = Runtime.getRuntime();
                final Process minisatd = runtime.exec("minisatd");
                BufferedReader stdout = new BufferedReader(new InputStreamReader(minisatd.getInputStream()));
                ExternalSpawner.MINISATD_PORT = Integer.parseInt(stdout.readLine());
                runtime.addShutdownHook(new Thread() {
                    @Override
                    public void run() {
                        minisatd.destroy();
                    }
                });
            } catch (Exception boom) {
                ExternalSpawner.log.log(Level.WARNING, "External spawner requested, but error starting it.", boom);
                ExternalSpawner.MINISATD_PORT = -1;
            }
        } else {
            ExternalSpawner.MINISATD_PORT = -1;
        }
    }

    public static boolean isSupported() {
        return (ExternalSpawner.MINISATD_PORT > 0) && TrackProcess.canTrackByPID();
    }

    public static Socket getSocket() throws IOException {
        if (! ExternalSpawner.isSupported()) {
            throw new IllegalArgumentException("external spawner requested, but not supported on this machine!");
        }
        return new Socket("127.0.0.1", ExternalSpawner.MINISATD_PORT);
    }
}
