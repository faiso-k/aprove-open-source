package aprove.verification.oldframework.Utility.Profiling;

import java.io.*;
import java.util.*;

import aprove.logging.*;

/**
 * stores some Information for Profiling Framework
 * @author Tim Enger
 */

public class Profiling {

    private static volatile Writer writer;

    /**
     * if true, profiling output is directly written to stderr <br>
     * so multiplexer is not used<br>
     * <b>without</b> FeatureVector and externString for Obligations <br>
     */
    public static boolean useMultiplexer = true;

    private static BitSet obligations;
    private static final Object syncObject = new Object();

    static {
        Profiling.obligations = new BitSet();
    }

    public static Writer getWriter() throws IOException {
        if (Profiling.writer == null) {
            synchronized (Profiling.syncObject) {
                if (Profiling.writer == null) {
                    Profiling.writer = AproveOutput.openWriter("profiling", true);
                }
            }
        }
        return Profiling.writer;
    }

    public static void addObligationId(int obl) {
        Profiling.obligations.set(obl);
    }

    public static boolean getObligationId(int obl) {
        return Profiling.obligations.get(obl);
    }

}
