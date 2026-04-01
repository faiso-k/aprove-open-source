package aprove.logging;

import java.io.*;
import java.util.logging.*;

public class CliLogFormatter extends Formatter {

    @Override
    public String format(LogRecord record) {
        String logString = this.formatMessage(record);
        if (logString.charAt(logString.length() - 1) != '\n') {
            logString += "\n";
        }
        Throwable excInfo = record.getThrown();
        if (excInfo != null) {
            StringWriter sw = new StringWriter();
            PrintWriter pw = new PrintWriter(sw);
            // TODO: find a way to limit this to only a few frames
            excInfo.printStackTrace(pw);
            pw.close();
            logString += sw.toString();
        }
        return logString;
    }

}
