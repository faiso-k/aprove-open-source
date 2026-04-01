package aprove.prooftree.Export.Utility;

/**
 * Implement this interface, if the string returned by toDOT() can be rendered using (only?) a recent version of dot
 * (but possibly not by JDotty).
 * @author cotto
 */
public interface DOTmodern_Able {
    /**
     * @return a string that can be rendered using a recent version of dot
     */
    String toDOT();
}
