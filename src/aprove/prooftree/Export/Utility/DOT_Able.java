package aprove.prooftree.Export.Utility;

/**
 * Implement this class, if the string returned by toDOT() can be rendered using JDotty.
 * @author Stephan Falke
 */
public interface DOT_Able extends DOTmodern_Able {
    /**
     * {@inheritDoc}
     */
    @Override
    String toDOT();
}
