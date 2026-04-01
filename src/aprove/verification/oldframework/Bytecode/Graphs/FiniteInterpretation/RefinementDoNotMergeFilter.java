package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

public class RefinementDoNotMergeFilter implements EdgeFilter {

    //no need to create more then one instance
    private RefinementDoNotMergeFilter() {}
    public static final RefinementDoNotMergeFilter INSTANCE = new RefinementDoNotMergeFilter();

    @Override
    public boolean selectEdge(Node from, Node to, EdgeInformation e) {
        if (e instanceof RefinementEdge) {
            return !((RefinementEdge) e).doNotMergeLoop();
        }
        return true;
    }

}
