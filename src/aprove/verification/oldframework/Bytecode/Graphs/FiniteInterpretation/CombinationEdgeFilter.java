package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

public class CombinationEdgeFilter implements EdgeFilter {

    private EdgeFilter[] filters;

    public CombinationEdgeFilter(EdgeFilter... filters) {
        this.filters = filters;
    }

    @Override
    public boolean selectEdge(Node from, Node to, EdgeInformation e) {
        for (int i=0; i<filters.length; i++) {
            if (!filters[i].selectEdge(from, to, e)) {
                return false;
            }
        }
        return true;
    }

}
