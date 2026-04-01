package aprove.verification.complexity.CpxRntsProblem.Algorithms;

import java.io.IOException;

public abstract class ProcessHelper {
    /**
     * Checks whether the given tool is installed by simply executing it
     * @warning this waits until the binary has returned!
     */
    public static boolean isInstalled(String tool) {
        try {
            Process p = Runtime.getRuntime().exec(tool);
            p.waitFor();
            return p.exitValue() != 127;
        } catch (IOException | InterruptedException e) {
            //ignore exception and assume that the tool is not installed
            return false;
        }
    }
}
