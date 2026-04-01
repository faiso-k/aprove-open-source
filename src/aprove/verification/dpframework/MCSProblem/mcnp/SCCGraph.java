package aprove.verification.dpframework.MCSProblem.mcnp;

import java.util.*;

public class SCCGraph {

    // vertexes with no neighbours is empty list
    Hashtable<String, String[]> _vertexesNeighbouring;
    List<List<String>> _components = new ArrayList<List<String>>();

    public SCCGraph(final Hashtable<String, String[]> vertexesNeighbouring) {
        this._vertexesNeighbouring = vertexesNeighbouring;
        this.buildSCC();
    }

    //0->1, 1->2, 2->0
    //3->4, 4->3
    //5

    //    index = 0                                         // DFS node number counter
    //    S = empty                                         // An empty stack of nodes
    //    forall v in V do
    //      if (v.index is undefined)                       // Start a DFS at each node
    //        tarjan(v)                                     // we haven't visited yet
    public List<List<Integer>> tarjan(final int[][] verticesIndexesNeighbouring) {
        final int[] index = {0 };
        final Stack<Integer> stack = new Stack<Integer>();
        final int[] componentIndex = new int[verticesIndexesNeighbouring.length];
        final int[] lowlinkIndex = new int[verticesIndexesNeighbouring.length];
        for (int i = 0; i < verticesIndexesNeighbouring.length; i++) {
            componentIndex[i] = -1;
            lowlinkIndex[i] = -1;
        }

        final List<List<Integer>> res = new ArrayList<List<Integer>>();
        for (int v = 0; v < componentIndex.length; v++) {
            if (componentIndex[v] < 0) {
                this.tarjan(v, index, componentIndex, lowlinkIndex, stack, verticesIndexesNeighbouring, res);
            }
        }
        return res;
    }

    //    procedure tarjan(v)
    //      v.index = index                                 // Set the depth index for v
    //      v.lowlink = index
    //      index = index + 1
    //      S.push(v)                                       // Push v on the stack
    //      forall (v, v') in E do                          // Consider successors of v
    //        if (v'.index is undefined)                    // Was successor v' visited?
    //            tarjan(v')                                // Recurse
    //            v.lowlink = min(v.lowlink, v'.lowlink)
    //        else if (v' is in S)                          // Was successor v' in stack S?
    //            v.lowlink = min(v.lowlink, v'.index )
    //      if (v.lowlink == v.index)                       // Is v the root of an SCC?
    //        print "SCC:"
    //        repeat
    //          v' = S.pop
    //          print v'
    //        until (v' == v)
    // index - current component index
    private void tarjan(final int v,
        final int[] index,
        final int[] componentIndex,
        final int[] lowlinkIndex,
        final Stack<Integer> stack,
        final int[][] verticesIndexesNeighbouring,
        final List<List<Integer>> resComponents) {
        componentIndex[v] = index[0];
        lowlinkIndex[v] = index[0];
        index[0] = index[0] + 1;
        stack.push(v);
        for (int i = 0; i < verticesIndexesNeighbouring[v].length; i++) {
            final int u = verticesIndexesNeighbouring[v][i];
            if (componentIndex[u] < 0) {
                this.tarjan(u, index, componentIndex, lowlinkIndex, stack, verticesIndexesNeighbouring, resComponents);
                lowlinkIndex[v] = Math.min(lowlinkIndex[v], lowlinkIndex[u]);
            } else if (stack.contains(u)) {
                lowlinkIndex[v] = Math.min(lowlinkIndex[v], componentIndex[u]);
            }
        }
        if (componentIndex[v] == lowlinkIndex[v]) {
            final List<Integer> component = new ArrayList<Integer>();
            int w = -1;
            do {
                w = stack.pop();
                component.add(w);
            } while (w != v);
            resComponents.add(component);
            //            System.out.println("SCC: "+Arrays.toString(component.toArray())); //D
        }
    }

    private void buildSCC() {
        // Vertexes neighbouring to vertexes indexes neighburing
        final Set<String> vertexesSet = this._vertexesNeighbouring.keySet();

        final String[] vertexesArray = new String[vertexesSet.size()];
        final Hashtable<String, Integer> vertexesToIndexesHT = new Hashtable<String, Integer>();

        // [vertexIndex, [neighbour1Index, neighbour2Index, ... ]
        final int[][] neighbouringIndexes = new int[vertexesArray.length][];

        int t = 0;
        for (final String vertex : vertexesSet) {
            vertexesArray[t] = vertex;
            vertexesToIndexesHT.put(vertex, t);
            t++;
        }

        for (int i = 0; i < vertexesArray.length; i++) {
            final String[] neighbours = this._vertexesNeighbouring.get(vertexesArray[i]);
            final int[] neighboursIndexes = new int[neighbours.length];
            for (int j = 0; j < neighbours.length; j++) {
                neighboursIndexes[j] = vertexesToIndexesHT.get(neighbours[j]);
            }
            neighbouringIndexes[i] = neighboursIndexes;
        }

        // Get GSS elements (indexes)
        final List<List<Integer>> indexNeighbouring = this.tarjan(neighbouringIndexes);

        // Translate vertexes indexes to vertexes
        for (final List<Integer> currentComponent : indexNeighbouring) {
            final List<String> currentComponentIDs = new ArrayList<String>();
            for (final Integer currentIndex : currentComponent) {
                currentComponentIDs.add(vertexesArray[currentIndex]);
            }
            this._components.add(currentComponentIDs);
            // Logger.writeReport("SCC: "+Arrays.toString(currentComponentIDs.toArray()));
        }

        //I THING THE ALGORITHM ALREADY RETURNS THE COMPONENTS TOPOLOGICALLY SORTED
        // SO THIS FUNCTION IS NOT NEEDED

        if (Config.LOG_BUILDING_SCC) {
            Logger.writeDebug("SCC components (before topologic sort): " + this._components);
        }

        this.topologicSort(this._vertexesNeighbouring, this._components);

        if (Config.LOG_BUILDING_SCC) {
            Logger.writeDebug("SCC components (after topologic sort): " + this._components);
        }
    }

    public List<List<String>> getSCCComponents() {
        return this._components;
    }

    //=====================================================
    public void topologicSort(final Hashtable<String, String[]> vertexesNeighbouring,
        final List<List<String>> gccComponents) {
        //Give each vertex it's component number in vertexComponentMappingHT <vertex, compontntNumber>
        final Hashtable<String, Integer> vertexComponentMappingHT = new Hashtable<String, Integer>();
        int compNumber = 0;
        for (final List<String> currentComp : gccComponents) {
            for (final String vertex : currentComp) {
                if (vertexComponentMappingHT.containsKey(vertex)) {
                    throw new RuntimeException("Vertex " + vertex + " appears in more than one component.");
                }
                vertexComponentMappingHT.put(vertex, compNumber);
            }
            compNumber++;
        }

        //build components neighbouring hashtable
        final Hashtable<Integer, Set<Integer>> componentNeighbouringHT = new Hashtable<Integer, Set<Integer>>();
        compNumber = 0;
        for (final Iterator<List<String>> compIt = gccComponents.iterator(); compIt.hasNext(); compIt.next()) {
            // compNumber component neighbouring components
            final Set<Integer> compNeighbours = new HashSet<Integer>();

            for (final String vertex : vertexesNeighbouring.keySet()) {
                final String[] vertexNeighbours = vertexesNeighbouring.get(vertex);
                // if current vertex is in compNumber component
                if (vertexComponentMappingHT.get(vertex).intValue() == compNumber) {
                    for (final String vertexNeighbour : vertexNeighbours) {
                        compNeighbours.add(vertexComponentMappingHT.get(vertexNeighbour));
                    }
                }
            }

            //remove self edges
            if (compNeighbours.contains(compNumber)) {
                compNeighbours.remove(compNumber);
            }
            componentNeighbouringHT.put(compNumber, compNeighbours);

            //scc component neighbouring
            //            if (Config.LOG_BUILDING_SCC)
            //                Logger.writeDebug("=======: "+compNumber+": "+compNeighbours); //D
            compNumber++;
        }

        // =============== topologic sort ===================
        // get graph root nodes
        final Set<Integer> nodesWithoutEnteringEdges = new HashSet<Integer>(componentNeighbouringHT.keySet());
        for (final Integer node : componentNeighbouringHT.keySet()) {
            final Set<Integer> enteringEdges = componentNeighbouringHT.get(node);
            nodesWithoutEnteringEdges.removeAll(enteringEdges);
        }
        if (Config.LOG_BUILDING_SCC) {
            Logger.writeDebug("Topologic sort roots: " + nodesWithoutEnteringEdges); //D
        }

        //component nodes in increasing topological order
        final List<Integer> sortedList = new ArrayList<Integer>();

        //visited vertexes
        final Set<Integer> visited = new HashSet<Integer>();
        for (final Integer integer : nodesWithoutEnteringEdges) {
            this.topologicSortVisit(integer, componentNeighbouringHT, sortedList, visited);
        }

        if (Config.LOG_BUILDING_SCC) {
            Logger.writeDebug("Topologically sorted components: " + sortedList);
        }

        //adjust components list to be sorted
        final List<List<String>> componentsTopologicallySorted = new ArrayList<List<String>>();
        for (final Integer integer : sortedList) {
            final int compNum = integer.intValue();
            componentsTopologicallySorted.add(this._components.get(compNum));
        }
        this._components = componentsTopologicallySorted;
    }

    //topologic sort helper function
    private void topologicSortVisit(final Integer node,
        final Hashtable<Integer, Set<Integer>> componentNeighbouringHT,
        final List<Integer> res,
        final Set<Integer> visited) {
        if (!visited.contains(node)) {
            visited.add(node);
            final Set<Integer> nodeNeighbours = componentNeighbouringHT.get(node);
            for (final Integer integer : nodeNeighbours) {
                this.topologicSortVisit(integer, componentNeighbouringHT, res, visited);
            }
            res.add(node);
        }
    }

}
