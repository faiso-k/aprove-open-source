package aprove.input.Programs.prolog;

/** represents one of three possible states: IN, OUT, NA
 * @author Christian Kaeunicke
 * @version $Id$
 */

public class ArgumentMode extends Object {
    
    private final int hashCode;
    
    /** used for input arguments */
    public static final ArgumentMode IN = new ArgumentMode(100);

    /** used for output arguments */
    public static final ArgumentMode OUT = new ArgumentMode(200);

    /** used for bounded lists arguments */
    public static final ArgumentMode LIST = new ArgumentMode(300);

    /** used for arguments of unknown mode */
    public static final ArgumentMode NA = new ArgumentMode(400);

    /** used for arguments that are overmoded by the ToHighlightedHTMLVisitor */
    public static final ArgumentMode OM = new ArgumentMode(500);

    /** used by modinference to mark those arguments that have to be infered */
    public static final ArgumentMode QMI = new ArgumentMode(600);

    protected int mode = 400;

    protected ArgumentMode(int mode) {
        this.mode = mode;
        this.hashCode = this.mode;
    };

    @Override
    public int hashCode() {
        return hashCode;
    }

    @Override
    public boolean equals(Object ox) {
    if (ox instanceof ArgumentMode) {
        return (((ArgumentMode) ox).mode == this.mode);
    } else {
        return false;
    }
    };

    @Override
    public String toString() {
    switch (this.mode) {
    case 100: return "GROUND";
    case 200: return "ANY";
    case 300: return "LIST";
    case 400: return "NA";
    case 500: return "OM";
    case 600: return "QMI";
    default: return "ERROR";
    }
    };

    public String toNameExtension() {
    switch (this.mode) {
    case 100: return "G";
    case 200: return "A";
    case 300: return "L";
    case 400: return "N";
    default: return "E";
    }
    };

    public String toHTML() {
    switch (this.mode) {
    case 100: return "g";
    case 200: return "a";
    case 300: return "l";
    case 400: return "na";
    case 500: return "om";
    case 600: return "?";
    default: return "err";
    }
    }
};
