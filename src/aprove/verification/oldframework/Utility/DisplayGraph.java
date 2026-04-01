package aprove.verification.oldframework.Utility;

import java.io.*;

public class DisplayGraph {

    public static void display(String dot) {
        DisplayGraph.display(dot,GraphOutputFormat.SVG);
    }

    public static void display(String dot,GraphOutputFormat format) {
        try {
            File dotFile = File.createTempFile("aprove.verification.oldframework.Utility.DisplayGraph", ".dot");
            dotFile.deleteOnExit();

            String outputExtension = format.toString().toLowerCase();
            File outputFile = File.createTempFile("aprove.verification.oldframework.Utility.DisplayGraph", "." + outputExtension);
            //svgFile.deleteOnExit();
            PrintWriter out = new PrintWriter(dotFile);
            out.write(dot);
            out.close();
            Process p = new ProcessBuilder("dot", "-T" + outputExtension, "-o", outputFile.getAbsolutePath(), dotFile.getAbsolutePath()).start();
            p.waitFor();


            String osName = System.getProperty("os.name");
            if (osName.startsWith("Linux")) {
                p = new ProcessBuilder("firefox", outputFile.getAbsolutePath()).start();
            } else if (osName.startsWith("Mac OS X")) {
                if(format == GraphOutputFormat.PNG || format == GraphOutputFormat.PDF) {
                    p = new ProcessBuilder("open", "-a", "Preview", outputFile.getAbsolutePath()).start();
                } else {
                    p = new ProcessBuilder("open", "-a", "Safari", outputFile.getAbsolutePath()).start();
                }
            } else if (osName.startsWith("Windows")) {
                if(format == GraphOutputFormat.PNG || format == GraphOutputFormat.PDF) {
                    //Use default application associated with type
                    Runtime.getRuntime().exec("cmd /c " + outputFile.getAbsolutePath());
                } else {
                    p = new ProcessBuilder("c:\\Programme\\Internet Explorer\\iexplore.exe", outputFile.getAbsolutePath()).start();
                }
            } else {
                throw new RuntimeException("Unknown OS name '" + osName +
                                           "'! Don't know which viewer to invoke.");
            }
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

    }


    public enum GraphOutputFormat {
        SVG,PNG,PDF

    }

}
