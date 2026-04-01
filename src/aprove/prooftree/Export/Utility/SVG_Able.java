package aprove.prooftree.Export.Utility;

import java.io.*;

/**
 * Implement this interface, if the file returned by toSVG() is a SVG file.
 * @author cotto
 */
public interface SVG_Able {
    /**
     * @return a file that is a SVG file.
     */
    File toSVG();
}
