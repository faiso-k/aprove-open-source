package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;

public class LevelMapping implements MCGraphMapping {
    // the ordering used with the current level mapping (ms_max_max_max, etc.)
    protected String _type;

    // for each program point store which arguments are in low/high sets
    protected Hashtable<String, Set<Integer>> _argumentsFilteringHi = new Hashtable<String, Set<Integer>>();
    protected Hashtable<String, Set<Integer>> _argumentsFilteringLo = new Hashtable<String, Set<Integer>>();

    protected Set<String> _mcGraphs = new HashSet<String>();

    // Used for ms/dms encoding parts
    // key - MC Graph ID, value <covered vertex, covering vertex>
    protected Hashtable<String, Hashtable<Integer, Integer>> _topToBottomCoverageHT =
        new Hashtable<String, Hashtable<Integer, Integer>>();
    protected Hashtable<String, Hashtable<Integer, Integer>> _bottomToTopCoverageHT =
        new Hashtable<String, Hashtable<Integer, Integer>>();
    protected Hashtable<String, Hashtable<Integer, Integer>> _topToTopCoverageHT =
        new Hashtable<String, Hashtable<Integer, Integer>>();
    protected Hashtable<String, Hashtable<Integer, Integer>> _bottomToBottomCoverageHT =
        new Hashtable<String, Hashtable<Integer, Integer>>();

    // Graph types according to the current level mapping
    protected Set<String> _graphsOrderedWeak = new HashSet<String>();
    protected Set<String> _graphsOrderedStrict = new HashSet<String>();
    // MCGs which may be removed
    protected Set<String> _graphsRemovable = new HashSet<String>();
    // MCGs which are in bound
    protected Set<String> _graphsInCutset = new HashSet<String>();

    // Numbers given to program points used to ensure bound/strict in cycles
    Hashtable<String, Integer> _progPointsBoundNumbering = new Hashtable<String, Integer>();
    Hashtable<String, Integer> _progPointsStrictNumbering = new Hashtable<String, Integer>();

    public LevelMapping(final String type) {
        this._type = type;
    }

    public String getType() {
        return this._type;
    }

    // Set low/high sets for the program point programPointID
    public void addProgramPoint(final String programPointID,
        final Set<Integer> filteredArgsHi,
        final Set<Integer> filteredArgsLo) {
        if (!this._argumentsFilteringHi.containsKey(programPointID)) {
            this._argumentsFilteringHi.put(programPointID, filteredArgsHi);
            this._argumentsFilteringLo.put(programPointID, filteredArgsLo);
        }
    }

    // Returns true if current level mapping refers to the programPointID
    public boolean containsProgramPoint(final String programPointID) {
        return this._argumentsFilteringHi.containsKey(programPointID);
    }

    // get program point high set
    public Set<Integer> getProgramPointFilteredArgumentsHi(final String programPointID) {
        return new HashSet<Integer>(this._argumentsFilteringHi.get(programPointID));
    }

    // get program point low set
    public Set<Integer> getProgramPointFilteredArgumentsLo(final String programPointID) {
        return new HashSet<Integer>(this._argumentsFilteringLo.get(programPointID));
    }

    // specify that mcgraphID is ordered weakly
    public void weakGraphOrdering(final String mcGraphID) {
        this._graphsOrderedWeak.add(mcGraphID);
    }

    // specify that mcgraphID is ordered strictly
    public void strictGraphOrdering(final String mcGraphID) {
        this._graphsOrderedStrict.add(mcGraphID);
    }

    // specify that mcgraphID may be removed
    public void strictRemovableGraphOrdering(final String mcGraphID) {
        this._graphsRemovable.add(mcGraphID);
    }

    // specify that mcgraphID is in bound
    public void graphInCutset(final String mcGraphID) {
        this._graphsInCutset.add(mcGraphID);
    }

    public Set<String> getWeakOrderedGraphs() {
        return this._graphsOrderedWeak;
    }

    public Set<String> getStrictOrderedGraphs() {
        return this._graphsOrderedStrict;
    }

    public Set<String> getRemovableGraphs() {
        return this._graphsRemovable;
    }

    public Set<String> getCutsetGraphs() {
        return this._graphsInCutset;
    }

    // return the number of vertex which covers v (used for ms/dms parts)
    public Integer getVertexCoverage(final Integer v, final String mcGraphID, final String direction) {
        Hashtable<String, Hashtable<Integer, Integer>> vertexCoverageHT = null;

        if (direction.equals(Constants.TOP_TO_BOTTOM)) {
            vertexCoverageHT = this._topToBottomCoverageHT;
        } else if (direction.equals(Constants.BOTTOM_TO_TOP)) {
            vertexCoverageHT = this._bottomToTopCoverageHT;
        } else if (direction.equals(Constants.TOP_TO_TOP)) {
            vertexCoverageHT = this._topToTopCoverageHT;
        } else if (direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            vertexCoverageHT = this._bottomToBottomCoverageHT;
        } else {
            throw new RuntimeException("Wrong coverage: " + direction);
        }

        if (vertexCoverageHT.containsKey(mcGraphID)) {
            final Hashtable<Integer, Integer> graphCoveringHT = vertexCoverageHT.get(mcGraphID);
            if (graphCoveringHT.containsKey(v)) {
                return graphCoveringHT.get(v);
            }
        }

        return null;
    }

    // specify that vertex v is covered by covering (used for ms/dms partd)
    public void addVertexCoverage(final Integer v,
        final Integer covering,
        final String mcGraphID,
        final String direction) {
        Hashtable<String, Hashtable<Integer, Integer>> vertexCoverageHT = null;

        if (direction.equals(Constants.TOP_TO_BOTTOM)) {
            vertexCoverageHT = this._topToBottomCoverageHT;
        } else if (direction.equals(Constants.BOTTOM_TO_TOP)) {
            vertexCoverageHT = this._bottomToTopCoverageHT;
        } else if (direction.equals(Constants.TOP_TO_TOP)) {
            vertexCoverageHT = this._topToTopCoverageHT;
        } else if (direction.equals(Constants.BOTTOM_TO_BOTTOM)) {
            vertexCoverageHT = this._bottomToBottomCoverageHT;
        } else {
            throw new RuntimeException("Wrong coverage: " + direction);
        }

        this._mcGraphs.add(mcGraphID);

        Hashtable<Integer, Integer> graphVeretexCoverage;
        if (!vertexCoverageHT.containsKey(mcGraphID)) {
            graphVeretexCoverage = new Hashtable<Integer, Integer>();
            vertexCoverageHT.put(mcGraphID, graphVeretexCoverage);
        }
        graphVeretexCoverage = vertexCoverageHT.get(mcGraphID);

        if (!graphVeretexCoverage.containsKey(v)) {
            graphVeretexCoverage.put(v, covering);
        }
    }

    //get program point bound numbering
    public Integer getProgPointBoundNumber(final String progPointID) {
        if (this._progPointsBoundNumbering.containsKey(progPointID)) {
            return this._progPointsBoundNumbering.get(progPointID);
        } else {
            return null;
        }
    }

    //get program point strict numbering
    public Integer getProgPointStrictNumber(final String progPointID) {
        if (this._progPointsStrictNumbering.containsKey(progPointID)) {
            return this._progPointsStrictNumbering.get(progPointID);
        } else {
            return null;
        }
    }

    //set program point bound numbering
    public void addProgPointBoundNumber(final String progPointID, final int num) {
        this._progPointsBoundNumbering.put(progPointID, num);
    }

    //set program point strict numbering
    public void addProgPointStrictNumber(final String progPointID, final int num) {
        this._progPointsStrictNumbering.put(progPointID, num);
    }

    // toString helper
    protected String coverageToString() {
        String res = "";

        final String[] directions =
            {Constants.TOP_TO_BOTTOM, Constants.BOTTOM_TO_TOP, Constants.TOP_TO_TOP, Constants.BOTTOM_TO_BOTTOM };
        final Hashtable[] directionCoverageHSs =
            {this._topToBottomCoverageHT, this._bottomToTopCoverageHT, this._topToTopCoverageHT,
                this._bottomToBottomCoverageHT };
        final String[] directionsTitles = {"Top->Bottom", "Bottom->Top", "Top->Top", "Bottom->Bottom" };

        for (final String mcGraphID : this._mcGraphs) {
            String graphCoverageString = "   MC Graph " + mcGraphID + " coverage:\n";

            for (int i = 0; i < directions.length; i++) {
                //graph: mcGraphID
                // direction: i
                String directionCoverageString = directionsTitles[i] + ": ";
                final Hashtable<String, Hashtable<Integer, Integer>> graphsCoveragesHT = (directionCoverageHSs[i]);
                if (graphsCoveragesHT.containsKey(mcGraphID)) {
                    final Hashtable<Integer, Integer> coverageHT = graphsCoveragesHT.get(mcGraphID);
                    for (final Integer vertex : coverageHT.keySet()) {
                        final Integer coveringVertex = coverageHT.get(vertex);
                        directionCoverageString += coveringVertex + "->" + vertex + " ";
                    }
                    graphCoverageString += "\t" + directionCoverageString + "\n";
                }
            }
            res += graphCoverageString;
        }
        return res;
    }

    // toString helper
    protected String progPointBoundNumberingToString() {
        String res = "   Program Points bound numbering: \n   \t";
        for (final String progPointID : this._progPointsBoundNumbering.keySet()) {
            res = res + progPointID + "=" + this.getProgPointBoundNumber(progPointID) + "; ";
        }
        return res + "\n";
    }

    // toString helper
    protected String progPointStrictNumberingToString() {
        String res = "   Program Points strict numbering: \n   \t";
        for (final String progPointID : this._progPointsStrictNumbering.keySet()) {
            res = res + progPointID + "=" + this.getProgPointStrictNumber(progPointID) + "; ";
        }
        return res + "\n";
    }

    @Override
    public String toString() {
        String res = "Level Mapping (type=" + this._type + "):\n";
        res += this.coverageToString();
        res += this.progPointBoundNumberingToString();
        res += this.progPointStrictNumberingToString();
        for (final String progPointID : this._argumentsFilteringHi.keySet()) {
            final Set<Integer> argumentsHi = this._argumentsFilteringHi.get(progPointID);
            final Set<Integer> argumentsLo = this._argumentsFilteringLo.get(progPointID);
            res =
                res + "   Program Point: " + progPointID + "\n" + "\tArguments: Low="
                    + Arrays.toString(argumentsLo.toArray()) + "; High=" + Arrays.toString(argumentsHi.toArray())
                    + "\n";
        }
        res = res + "   Weakly ordered MC Graphs: " + Arrays.toString(this._graphsOrderedWeak.toArray()) + "\n";
        if (Config.CUTSET_METHOD) {
            res = res + "   Strictly ordered MC Graphs: " + Arrays.toString(this._graphsOrderedStrict.toArray()) + "\n";
            res = res + "   Anchors MC Graphs: " + Arrays.toString(this._graphsRemovable.toArray()) + "\n";
            res = res + "   Bounded MC Graphs: " + Arrays.toString(this._graphsInCutset.toArray()) + "\n";
        } else {
            res = res + "   Strictly ordered MC Graphs: " + Arrays.toString(this._graphsOrderedStrict.toArray()) + "\n";
        }
        return res + "\n";
    }
}
