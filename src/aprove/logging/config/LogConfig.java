package aprove.logging.config;

import java.io.*;
import java.util.logging.*;

public class LogConfig {

    private static boolean userProvidedConfig() {
        String loggingConfigClass = System.getProperty("java.util.logging.config.class");
        String loggingConfigFile = System.getProperty("java.util.logging.config.file");
        return loggingConfigClass != null || loggingConfigFile != null;
    }

    public static void init(String logConfig) {
        if (userProvidedConfig()) {
            return;
        }
        InputStream stream = LogConfig.class.getResourceAsStream(logConfig + ".properties");
        try {
            LogManager.getLogManager().readConfiguration(stream);
            stream.close();
        } catch (IOException e) {
            System.err.println("Error configuring logging!");
            e.printStackTrace();
        }
    }

}
