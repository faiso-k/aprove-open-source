package aprove.input.Programs.loat.debug;

import java.io.*;

public class FileWriter {
    
    public static void dumpString(String dump, String filename) {
        PrintWriter writer;
        try {
            writer = new PrintWriter(filename, "UTF-8");
            writer.print(dump);
            writer.close();
        } catch (Exception e) {
            System.err.println(e.getMessage());
        }
    }

}
