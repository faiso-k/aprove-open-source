package aprove.verification.oldframework.IntTRS.TerminationGraph;

/**
 * Some colors used to color the graph. The colors have we following semantics:
 * GRAY: Don't touch these rules. BLUE & RED: to be replaced by "chained"
 * versions!
 * @author Matthias Hoelzel
 */
public enum RedGrayBlue {
    /** To be dropped! */
    RED,
    /** To be kept! */
    GRAY,
    /** To be replaced! */
    BLUE;
}
