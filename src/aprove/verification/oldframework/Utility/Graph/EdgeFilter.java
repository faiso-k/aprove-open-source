package aprove.verification.oldframework.Utility.Graph;

public interface EdgeFilter<E,N> {

    public boolean selectEdge(Node<N> source, Node<N> dest, E label);

}
