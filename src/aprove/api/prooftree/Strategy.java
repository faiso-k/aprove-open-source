package aprove.api.prooftree;

import java.io.*;
import java.nio.file.*;
import java.util.*;

/**
 * Represents the strategy for the analysis.
 */
public class Strategy {

    public static Strategy fromModuleName(String moduleName) {
        Objects.requireNonNull(moduleName);
        return new Strategy(true, moduleName);
    }

    public static Strategy fromPath(Path path) throws IOException {
        Objects.requireNonNull(path);
        return new Strategy(false, readContents(path));
    }

    private static String readContents(Path path) throws IOException {
        return new String(Files.readAllBytes(path));
    }

    private final boolean isModuleName;
    private final String text;

    private Strategy(boolean isModuleName, String text) {
        this.isModuleName = isModuleName;
        this.text = text;
    }

    public boolean isModuleName() {
        return isModuleName;
    }

    public String getText() {
        return text;
    }
}
