package aprove.api.decisions.impl;

import java.io.*;
import java.util.*;

public enum LocalToolDetector {
    ;

    /**
     * @return true, iff the tool with the given name exists on the local machine.
     */
    public static boolean cintBackendExists(String toolName) {
        try {
            Process p = Runtime.getRuntime().exec(toolName);
            p.waitFor();
            int exitValue = p.exitValue();
            return !Arrays.asList(127 /* Linux */, 9009 /* Windows */).contains(exitValue);
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
            return false;
        }
    }

}
