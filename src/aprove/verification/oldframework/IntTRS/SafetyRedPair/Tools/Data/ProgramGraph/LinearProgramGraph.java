package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.ProgramGraph.Locations.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.LinearTransitionPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.TransitionPair.TermTransitionPair.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Linear program graph, the transition are defined by linear relations and linear constraints systems.
 * The linear program is created from flattening of an arithmetic program (ProgramGraph).
 * The non-linear terms, both in the relations and in the conditions are replaced by fresh variable.
 * @author marinag
 *
 */
public class LinearProgramGraph extends SimpleGraph<LocationID, LinearTransitionPairsSet> {
    Location root;

    /**
     * Maps each non-linear function symbol to a fresh variable that substituted an application of this symbol
     */
    final Map<FunctionSymbol, Set<String>> fSymToVars;

    /**
     * Maps each fresh variable to the function application it substitutes and the list of its variable arguments
     */
    final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp;


    /**
     * Maps each edge of the initial program to the linear edge that replaced it in this linear program
     */
    private final Map<Edge<TermTransitionPairsSet, LocationID>, Edge<LinearTransitionPairsSet, LocationID>> toLinEdge =
        new HashMap<>();

        /**
         * The reverse of the mapping toLinEdge
         */
        private final Map<Edge<LinearTransitionPairsSet, LocationID>, Edge<TermTransitionPairsSet, LocationID>> toOrigEdge =
            new HashMap<>();

            /**
             * Generator for the fresh variables names
             */
            private final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);


    /**
     * @param pg
     */
            public LinearProgramGraph(final ProgramGraph pg) {
                super();

                this.fSymToVars = new HashMap<>();
                this.varsToFApp = new HashMap<>();
                this.root = pg.getStartLocation();
                this.addNode(this.root);

                for (final Edge<TermTransitionPairsSet, LocationID> edge : pg.getEdges()) {
                    final Edge<LinearTransitionPairsSet, LocationID> linEdge =
                        new Edge<>(
                            edge.getStartNode(),
                            edge.getEndNode(),
                            edge.getObject().flatten(this.fSymToVars, this.varsToFApp, this.ng));

                        this.addEdge(linEdge);
                        this.toLinEdge.put(edge, linEdge);
                        this.toOrigEdge.put(linEdge, edge);
                }

                for (final Edge<LinearTransitionPairsSet, LocationID> edge : this.getEdges()) {
                    edge.getObject().extendUndefined(this.varsToFApp);
                }
            }

    /**
     *
     */
            public LinearProgramGraph() {
                super();

                this.fSymToVars = new HashMap<>();
                this.varsToFApp = new HashMap<>();
            }

    /**
     * @param root
     * @param edges
     * @param varsToFApp
     * @param fSymToVars
     */
            public LinearProgramGraph(
                final Location root,
                final Set<Edge<LinearTransitionPairsSet, LocationID>> edges,
                final Map<String, Pair<TRSFunctionApplication, List<String>>> varsToFApp,
                final Map<FunctionSymbol, Set<String>> fSymToVars)
            {

                super();
                this.addNode(root);
                this.varsToFApp = varsToFApp;
                this.fSymToVars = fSymToVars;
                for (final Edge<LinearTransitionPairsSet, LocationID> edge : edges) {
                    this.addEdge(edge);
                }
                this.root = root;
            }

    /**
     * @param edge
     * @return
     */
            public
            Edge<LinearTransitionPairsSet, LocationID>
            getLinearEdge(final Edge<TermTransitionPairsSet, LocationID> edge)
            {
                final Edge<LinearTransitionPairsSet, LocationID> linEdge = this.toLinEdge.get(edge);

                if (linEdge != null && this.contains(linEdge.getStartNode(), linEdge.getEndNode())) {
                    return linEdge;
                }

                return null;
            }

    /**
     * @param edge
     * @return
     */
            public Edge<TermTransitionPairsSet, LocationID> getOriginalEdge(
                final Edge<LinearTransitionPairsSet, LocationID> edge)
                {
                return this.toOrigEdge.get(edge);
                }

            public TRSSubstitution getSubstitution() {
                final Map<TRSVariable, TRSFunctionApplication> map = new HashMap<>();

                for (final Entry<String, Pair<TRSFunctionApplication, List<String>>> entry : this.varsToFApp.entrySet()) {
                    map.put(TRSTerm.createVariable(entry.getKey()), entry.getValue().x);
                }

                return TRSSubstitution.create(ImmutableCreator.create(map));
            }

    /**
     * @return
     */
            public Map<FunctionSymbol, Set<String>> getFSymToVars() {
                return this.fSymToVars;
            }

    /**
     * @return
     */
            public Map<String, Pair<TRSFunctionApplication, List<String>>> getVarsToFApp() {
                return this.varsToFApp;
            }

    /**
     * @return
     */
            public Location getStartLocation() {
                return this.root;
            }

    /**
     * @return
     */
            public FreshNameGenerator getFrshNameGenerator() {
                return this.ng;
            }

    /**
     * @param s program edge
     * @return splits the edge s in such way that each edge in the list has only one transition pair
     */
            public static List<Edge<LinearTransitionPair, LocationID>> splitEdge(
                final Edge<LinearTransitionPairsSet, LocationID> s)
                {
                final List<Edge<LinearTransitionPair, LocationID>> edges = new ArrayList<>();

                for (final LinearTransitionPair d : s.getObject()) {
                    edges.add(new Edge<>(s.getStartNode(), s.getEndNode(), d));
                }
                return edges;
                }


            @Override
            public String toString() {
                final StringBuilder builder = new StringBuilder();

                builder.append("UnwindingGraph\n");

                if (this.root != null) {
                    builder.append("Start: " + this.root.toString() + "\n");
                }

                builder.append("\nFresh Variables:\n");

                for (final Entry<String, Pair<TRSFunctionApplication, List<String>>> entry : this.varsToFApp.entrySet()) {
                    builder.append(entry.getKey() + " = " + entry.getValue().x + "\n");
                }

                builder.append("\nEdges:\n");

                for (final Edge<LinearTransitionPairsSet, LocationID> edge : this.getEdges()) {
                    builder.append(edge.toString() + "\n");
                }


                return builder.toString();
            }

}
