package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

/**
 * For a given node, provide more info (e.g. the color) to be used in the dot output.
 * @author cotto
 */
public interface AdditionalNodeInfoProvider {
    /**
     * @param node a node
     * @return the color that should be used for the node (null for defaults)
     */
    String getColor(Node node);

    /**
     * @param node a node
     * @return a dot string that should be prepended to the normal node string
     */
    String getPrependString(Node node);

    /**
     *
     * @param node a node
     * @return a dot string that should be appended to the normal node string
     */
    String getAppendString(Node node);
}
