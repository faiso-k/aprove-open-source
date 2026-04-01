package aprove.verification.dpframework.MCSProblem.mcnp;

import java.io.*;
import java.util.*;

import aprove.verification.dpframework.MCSProblem.*;
import aprove.verification.dpframework.MCSProblem.graphics.*;
import aprove.verification.dpframework.MCSProblem.sat_tools.*;
import immutables.*;

public class Program {

    // <ID,ProgramPoint>
    private final Hashtable<String, ProgramPoint> _programPoints = new Hashtable<String, ProgramPoint>();
    // <ID,MCGraph>
    private final Hashtable<String, MCGraph> _mcGraphs = new Hashtable<String, MCGraph>();

    // This list does not change after the program is initiated.
    // For external usages later.
    private List<MCGraph> _initialMCGraphsList = new ArrayList<MCGraph>();

    // contains ranking function in the end
    private List<MCGraphMapping> _mcGraphsMappings = new ArrayList<MCGraphMapping>();

    private final Timer _timer = new Timer();
    private MCGraph _biggestMCG = null; //MCG having most edges
    private MCGraph _biggestMCGNodes = null; //MCG having most nodes
    private MCGraph _biggestMCGNodesPerProgramPoint = null; //MCG having prog point with most nodes

    public void addProgramPoint(final ProgramPoint programPoint) {
        this._programPoints.put(programPoint.getID(), programPoint);
    }

    // add MC Graph to program and it's two program points
    public void addMCGraph(final MCGraph mcGraph) {
        this._mcGraphs.put(mcGraph.getID(), mcGraph);
        this.addProgramPoint(mcGraph.getPointFrom());
        this.addProgramPoint(mcGraph.getPointTo());
    }

    public boolean removeMCGraph(final String mcGraphID) {
        if (this._mcGraphs.containsKey(mcGraphID)) {
            this._mcGraphs.remove(mcGraphID);
            return true;
        } else {
            return false;
        }
    }

    // return the list of all program points
    public List<ProgramPoint> getProgramPoints() {
        final List<ProgramPoint> res = new ArrayList<ProgramPoint>();
        for (final String string : this._programPoints.keySet()) {
            res.add(this._programPoints.get(string));
        }
        return res;
    }

    // return the set of ProgramPoint-s involved in mcGraphs
    public Set<ProgramPoint> getGraphsProgramPoints(final List<MCGraph> mcGraphs) {
        final Set<ProgramPoint> programPoints = new HashSet<ProgramPoint>();
        for (final MCGraph mcGraph : mcGraphs) {
            programPoints.add(mcGraph.getPointFrom());
            programPoints.add(mcGraph.getPointTo());
        }
        return programPoints;
    }

    // return the list of all MC Graphs
    public List<MCGraph> getMCGraphs() {
        final List<MCGraph> res = new ArrayList<MCGraph>();
        for (final String string : this._mcGraphs.keySet()) {
            res.add(this._mcGraphs.get(string));
        }
        return res;
    }

    // return the list of all MC Graphs as after the initiation
    public List<MCGraph> getInitialMCGraphs() {
        return this._initialMCGraphsList;
    }

    // return MCGs involving program points IDs
    public List<MCGraph> getMCGraphs(final List<String> progPointsIDs) {
        final Set<String> progPointsIDsSet = new HashSet<String>(progPointsIDs);
        final List<MCGraph> res = new ArrayList<MCGraph>();
        for (final String string : this._mcGraphs.keySet()) {
            final MCGraph mcg = this._mcGraphs.get(string);
            if (progPointsIDsSet.contains(mcg.getPointFrom().getID())
                && progPointsIDsSet.contains(mcg.getPointTo().getID())) {
                res.add(mcg);
            }
        }
        return res;
    }

    // merge graphs having one one entering or exiting edge.
    public MCGraph mergeGraphs(final MCGraph mcg1, final MCGraph mcg2) {
        if (Config.LOG_MERGING_GRAPHS) {
            Logger.write("Merge MC Graphs: " + mcg1.getID() + " and " + mcg2.getID());
            Logger.writeDebug(mcg1 + " " + mcg2);
        }

        final String VAR_PREFIX = "v_";
        final String FROM_ARG_PREFIX = "#x";
        final String TO_ARG_PREFIX = "#y";

        final Argument[] point1FromArgs = mcg1.getPointFrom().getArguments();
        final Argument[] point1ToArgs = mcg1.getPointTo().getArguments();
        final Argument[] point2FromArgs = mcg2.getPointFrom().getArguments();
        final Argument[] point2ToArgs = mcg2.getPointTo().getArguments();

        if (!mcg1.getPointTo().getID().equals(mcg2.getPointFrom().getID())) {
            throw new RuntimeException("Can not concatinate graphs: " + mcg1 + " and " + mcg2 + ".");
        }

        // ---------------- Build all vertexes neighbouring ------------------

        //key=vertes, value=[ {neighbours strictly}, {neighbours weakly} ]
        Hashtable<String, Set<String>[]> neighbouringHT = new Hashtable<String, Set<String>[]>();

        final int[] argsFromLevel = {0, 1, 1, 2, 0, 1, 1, 2 };
        final int[] argsToLevel = {0, 1, 1, 2, 1, 0, 2, 1 };

        final Argument[][] argsFrom =
            {point1FromArgs, point1ToArgs, point2FromArgs, point2ToArgs, point1FromArgs, point1ToArgs, point2FromArgs,
                point2ToArgs };
        final Argument[][] argsTo =
            {point1FromArgs, point1ToArgs, point2FromArgs, point2ToArgs, point1ToArgs, point1FromArgs, point2ToArgs,
                point2FromArgs };

        final MCGraph[] mcGraphs = {mcg1, mcg1, mcg2, mcg2, mcg1, mcg1, mcg2, mcg2 };

        for (int k = 0; k < argsFrom.length; k++) {
            final MCGraph currMcg = mcGraphs[k];
            final int currArgLevelFrom = argsFromLevel[k];
            final Argument[] currLevelArgsFrom = argsFrom[k];
            final int currArgLevelTo = argsToLevel[k];
            final Argument[] currLevelArgsTo = argsTo[k];

            for (int i = 0; i < currLevelArgsFrom.length; i++) {
                final String vertex = VAR_PREFIX + currArgLevelFrom + "," + i;

                if (!neighbouringHT.containsKey(vertex)) {
                    final Set<String>[] neighbours = new Set[2];
                    neighbours[0] = new HashSet<String>();
                    neighbours[1] = new HashSet<String>();
                    neighbouringHT.put(vertex, neighbours);
                }

                for (int j = 0; j < currLevelArgsTo.length; j++) {
                    final String relationType = currMcg.getRelation(currLevelArgsFrom[i], currLevelArgsTo[j]);
                    if (relationType != null) {
                        final String neighbour = VAR_PREFIX + currArgLevelTo + "," + j;
                        final Set<String>[] neighbours = neighbouringHT.get(vertex);
                        if (relationType.equals(">")) {
                            neighbours[0].add(neighbour);
                            if (neighbours[1].contains(neighbour)) {
                                neighbours[1].remove(neighbour);
                            }
                        } else if (relationType.equals(">=")) {
                            if (!neighbours[0].contains(neighbour)) {
                                neighbours[1].add(neighbour);
                            }
                        }
                    } //if: edge exists
                } //for: to vertex
            } //for: from vertex
        } //for: edges among the same program point (4 program points)

        // ============= transitive closure ========================
        boolean updated = true;

        while (updated) {
            updated = false;
            // transitive closure - once
            final Hashtable<String, Set<String>[]> nextNeighbouringHT = new Hashtable<String, Set<String>[]>();
            for (final String vertex : neighbouringHT.keySet()) {
                final Set<String>[] neighbours = neighbouringHT.get(vertex);
                final Set<String> strict = neighbours[0];
                final Set<String> weak = neighbours[1];

                final Set<String> nextStrict = new HashSet<String>();
                final Set<String> nextWeak = new HashSet<String>();
                final Set[] allNeighbours = {nextStrict, nextWeak };
                nextNeighbouringHT.put(vertex, allNeighbours);

                nextStrict.addAll(strict);
                nextWeak.addAll(weak);

                for (final String neighbour : strict) {
                    //if strict v->n then add all n neighbours with strict edge as v neighbours
                    nextStrict.addAll(neighbouringHT.get(neighbour)[0]);
                    nextStrict.addAll(neighbouringHT.get(neighbour)[1]);
                }

                for (final String neighbour : weak) {
                    //if strict v->n then add all n neighbours with strict edge as v neighbours
                    nextStrict.addAll(neighbouringHT.get(neighbour)[0]);
                    nextWeak.addAll(neighbouringHT.get(neighbour)[1]);
                }

                nextWeak.removeAll(nextStrict);
                if (nextWeak.contains(vertex)) {
                    nextWeak.remove(vertex);
                }

                updated = updated || strict.size() != nextStrict.size() || weak.size() != nextWeak.size();
            }
            neighbouringHT = nextNeighbouringHT;
        }

        // ======================= graph to MC Graph ======================
        final List<String[]> relations = new ArrayList<String[]>();

        final String[] fromPrefixes = {FROM_ARG_PREFIX, FROM_ARG_PREFIX, TO_ARG_PREFIX, TO_ARG_PREFIX };
        final String[] toPrefixes = {FROM_ARG_PREFIX, TO_ARG_PREFIX, FROM_ARG_PREFIX, TO_ARG_PREFIX };
        final int[] fromLevels = {0, 0, 2, 2 };
        final int[] toLevels = {0, 2, 0, 2 };
        final int[] fromArgsNum =
            {point1FromArgs.length, point1FromArgs.length, point2ToArgs.length, point2ToArgs.length };
        final int[] toArgsNum =
            {point1FromArgs.length, point2ToArgs.length, point1FromArgs.length, point2ToArgs.length };

        for (int k = 0; k < fromPrefixes.length; k++) {
            final String fromPrefix = fromPrefixes[k];
            final String toPrefix = toPrefixes[k];
            final int fromLevel = fromLevels[k];
            final int toLevel = toLevels[k];

            for (int i = 0; i < fromArgsNum[k]; i++) {
                final String vertex = VAR_PREFIX + fromLevel + "," + i;
                final Set<String>[] neighbours = neighbouringHT.get(vertex);
                final Set<String> strict = neighbours[0];
                final Set<String> weak = neighbours[1];

                for (int j = 0; j < toArgsNum[k]; j++) {
                    final String neighbour = VAR_PREFIX + toLevel + "," + j;
                    if (strict.contains(neighbour)) {
                        final String[] rel = {fromPrefix + i, toPrefix + j, ">" };
                        relations.add(rel);
                    } else if (weak.contains(neighbour)) {
                        final String[] rel = {fromPrefix + i, toPrefix + j, ">=" };
                        relations.add(rel);
                    }
                }
            }
        }

        final String[] newPointFromArgs = new String[point1FromArgs.length];
        for (int i = 0; i < newPointFromArgs.length; i++) {
            newPointFromArgs[i] = FROM_ARG_PREFIX + i;
        }
        final ProgramPoint newPointFrom = new ProgramPoint(mcg1.getPointFrom().getPointName(), newPointFromArgs);

        final String[] newPointToArgs = new String[point2ToArgs.length];
        for (int i = 0; i < newPointToArgs.length; i++) {
            newPointToArgs[i] = TO_ARG_PREFIX + i;
        }
        final ProgramPoint newPointTo = new ProgramPoint(mcg2.getPointTo().getPointName(), newPointToArgs);

        final String[][] relationsAsArray = new String[relations.size()][];
        int ind = 0;
        for (final String[] name : relations) {
            relationsAsArray[ind] = name;
            ind++;
        }

        final MCGraph newMCGraph = new MCGraph(newPointFrom, newPointTo, relationsAsArray);

        if (Config.LOG_MERGING_GRAPHS) {
            Logger.write("Result MC Graph: " + newMCGraph.getID());
            Logger.writeDebug(newMCGraph + "");
        }

        return newMCGraph;
    }

    // while there is program point p with one entering edge q->p
    //merge q->p with all graphs a->q,b->q, ...
    //and the same with one exiting edge
    public List<MCGraph> mergeGraphs(List<MCGraph> mcGraphs) {
        if (Config.LOG_MERGING_GRAPHS) {
            Logger.write("======================= Merge MC Graphs: =============================");
        }

        boolean updated = true;
        while (updated) { //while some graphs were merged
            updated = false;

            //build neighbouring
            final Hashtable<String, List<MCGraph>> exitingEdgesHT = new Hashtable<String, List<MCGraph>>();
            final Hashtable<String, List<MCGraph>> enteringEdgesHT = new Hashtable<String, List<MCGraph>>();
            for (final MCGraph mcg : mcGraphs) {
                final String pointFromID = mcg.getPointFrom().getID();
                final String pointToID = mcg.getPointTo().getID();
                if (!exitingEdgesHT.containsKey(pointFromID)) {
                    exitingEdgesHT.put(pointFromID, new ArrayList<MCGraph>());
                }
                if (!exitingEdgesHT.containsKey(pointToID)) {
                    exitingEdgesHT.put(pointToID, new ArrayList<MCGraph>());
                }
                exitingEdgesHT.get(pointFromID).add(mcg);

                if (!enteringEdgesHT.containsKey(pointFromID)) {
                    enteringEdgesHT.put(pointFromID, new ArrayList<MCGraph>());
                }
                if (!enteringEdgesHT.containsKey(pointToID)) {
                    enteringEdgesHT.put(pointToID, new ArrayList<MCGraph>());
                }
                enteringEdgesHT.get(pointToID).add(mcg);
            }

            //graphs removed in the current iteration
            final Set<String> removedGraphsIDs = new HashSet<String>();
            //graphs added in the current iteration
            final List<MCGraph> addedGraphs = new ArrayList<MCGraph>();

            for (final Iterator<String> itProgPoints = exitingEdgesHT.keySet().iterator(); itProgPoints.hasNext()
                && !updated;) {
                final String progPointID = itProgPoints.next();
                final List<MCGraph> exitingEdges = exitingEdgesHT.get(progPointID);
                final List<MCGraph> enteringEdges = enteringEdgesHT.get(progPointID);

                if (exitingEdges.size() == 1
                    && !exitingEdges.get(0).getPointFrom().getID().equals(exitingEdges.get(0).getPointTo().getID())
                    && enteringEdges.size() > 0) {
                    final MCGraph exitingEdge = exitingEdges.get(0);
                    for (final MCGraph enteringEdge : enteringEdges) {
                        // do not merge self edge to itself
                        if (!exitingEdge.getID().equals(enteringEdge.getID())) {
                            final MCGraph newEdge = this.mergeGraphs(enteringEdge, exitingEdge);
                            removedGraphsIDs.add(exitingEdge.getID());
                            removedGraphsIDs.add(enteringEdge.getID());
                            addedGraphs.add(newEdge);
                            updated = true;
                        }
                    }
                }
            } //for

            if (!updated) { //if no prog point with one exiting edge try to find with one entering
                for (final Iterator<String> itProgPoints = enteringEdgesHT.keySet().iterator(); itProgPoints.hasNext()
                    && !updated;) {
                    final String progPointID = itProgPoints.next();
                    final List<MCGraph> exitingEdges = exitingEdgesHT.get(progPointID);
                    final List<MCGraph> enteringEdges = enteringEdgesHT.get(progPointID);

                    if (enteringEdges.size() == 1
                        && !enteringEdges.get(0).getPointFrom().getID().equals(
                            enteringEdges.get(0).getPointTo().getID()) && exitingEdges.size() > 0) {
                        final MCGraph enteringEdge = enteringEdges.get(0);
                        for (final MCGraph exitingEdge : exitingEdges) {
                            // do not merge self edge to itself
                            if (!exitingEdge.getID().equals(enteringEdge.getID())) {
                                final MCGraph newEdge = this.mergeGraphs(enteringEdge, exitingEdge);
                                removedGraphsIDs.add(exitingEdge.getID());
                                removedGraphsIDs.add(enteringEdge.getID());
                                addedGraphs.add(newEdge);
                                updated = true;
                            }
                        }
                    }
                } //for
            } //if not updated

            // update graphs list
            final List<MCGraph> newMCGraphs = new ArrayList<MCGraph>();
            for (final MCGraph mcg : mcGraphs) {
                if (!removedGraphsIDs.contains(mcg.getID())) {
                    newMCGraphs.add(mcg);
                }
            }
            newMCGraphs.addAll(addedGraphs);
            mcGraphs = newMCGraphs;

        } //while updated

        return mcGraphs;
    }

    private Program(final BufferedReader br) {
        // f(x1, x2, x3) :- [x1>=y1, x3>y2, x2>=y3] ; g(y1, y2, y3).
        // g(x1, x2, x3) :- [x3>=y1, x2>y2, x1>=y3] ; f(y1, y2, y3).
        final List<MCGraph> inputFileMCGraphs = new ArrayList<MCGraph>(); //list of graphs readed from the input
        try {
            if (Config.LOG_READING_INPUT) {
                Logger.writeReport("\n++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
                Logger.writeReport("++++++++++++++++++++++++++++++++++ Reading MC Graphs from file. +++++++++++++++++++++++++++++++++++++");
                //                Logger.writeReport(inputFile);
                Logger.writeReport("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
            }
            boolean comment = false; //currently reading comment
            String line = "";
            String[] graphs = null;
            String[] graphParts = null; // from :- relations ; to.
            line = br.readLine(); // read line possibly with few graphs
            while (line != null) {
                if (line.trim().length() > 0 && !line.trim().startsWith("#") && !line.trim().startsWith("%")) {
                    // System.out.println(line);
                    if (line.trim().endsWith("*/")) {
                        comment = false;
                        line = br.readLine();
                        continue;
                    } else if (line.trim().startsWith("/*") || comment) {
                        comment = true;
                        line = br.readLine();
                        continue;
                    }
                    graphs = line.trim().split("[.]");
                    for (final String graph : graphs) {
                        //                        if (graphs[i].split("\\(").length!=2)
                        //                            System.out.println("(");
                        //                        if (graphs[i].split("\\)").length!=2)
                        //                            System.out.println(")");
                        //                        if (graphs[i].split("\\[").length!=2)
                        //                            System.out.println("[");
                        //                        if (graphs[i].split("\\]").length!=2)
                        //                            System.out.println("]");
                        //                        if (1==1)    continue;
                        //                        String regex = ".*(.*)(\\w)*\\[(.*)\\]";
                        //                        Pattern pattern = Pattern.compile(regex);
                        //                        System.out.println(pattern);
                        //                        if (1==1) return;
                        // p(...) :- [...] , q(...) => p(...) :- [...] ; q(...)
                        //                        if (line.indexOf(";")<0) {
                        //                            graphs[i]=graphs[i].trim();
                        //                            int ind = line.lastIndexOf("]")+1;
                        //                            String beforeComma = graphs[i].substring(0,ind);
                        //                            String afterComma = graphs[i].substring(ind+1).trim();
                        //                            graphs[i] = beforeComma+";"+afterComma;
                        //                        }

                        //graphParts = graphs[i].split("(:-)|(;)");
                        if (graph.indexOf(";") >= 0) {
                            graphParts = graph.split("(:-)(\\s)*\\[|(\\](\\s)*[;])");
                        } else {
                            graphParts = graph.split("(:-)(\\s)*\\[|(\\](\\s)*[,])");
                        }
                        //                        System.out.println("=-==\n"+graphParts[0]+"\n"+graphParts[1]+"\n"+graphParts[2]);
                        if (graphParts.length != 3) {
                            Logger.writeError("Invalid input: " + line);
                        }

                        // parse program point from
                        final String progPointFrom = graphParts[0].trim();
                        int ind = progPointFrom.lastIndexOf("(");
                        final String programPointFromName = progPointFrom.substring(0, ind).trim();
                        final String programPointFromArgs =
                            progPointFrom.substring(ind + 1, progPointFrom.length() - 1).trim();

                        //                        String[] progPointFromSplitted = progPointFrom.split("\\(|\\)");
                        //                        String programPointFromName = progPointFromSplitted[0];
                        String[] progPointFromArguments = new String[0]; //no vars
                        //                        if (progPointFromSplitted.length>1 && progPointFromSplitted[1].trim().length()>0)
                        //                            progPointFromArguments = CommonOperations.trimStringArray(progPointFromSplitted[1].split(","));
                        if (programPointFromArgs.length() > 0) {
                            progPointFromArguments = CommonOperations.trimStringArray(programPointFromArgs.split(","));
                        }

                        //                        System.out.println(programPointFromName+" "+Arrays.toString(progPointFromArguments));

                        // parse program point to
                        final String progPointTo = graphParts[2].trim();
                        ind = progPointTo.lastIndexOf("(");
                        final String programPointToName = progPointTo.substring(0, ind).trim();
                        final String programPointToArgs = progPointTo.substring(ind + 1, progPointTo.length() - 1).trim();

                        //                        String[] progPointToSplitted = progPointTo.split("\\(|\\)");
                        //                        String programPointToName = progPointToSplitted[0];
                        String[] progPointToArguments = new String[0]; //no vars
                        //                        if (progPointToSplitted.length>1 && progPointToSplitted[1].trim().length()>0)
                        //                            progPointToArguments = CommonOperations.trimStringArray(progPointToSplitted[1].split(","));
                        if (programPointToArgs.length() > 1) {
                            progPointToArguments = CommonOperations.trimStringArray(programPointToArgs.split(","));
                        }

                        //                        System.out.println(programPointToName+" "+Arrays.toString(progPointToArguments));

                        //                        if (progPointFromSplitted.length > 2 || progPointToSplitted.length > 2)
                        //                            Logger.writeError("Invalid program points in input: "+ line);
                        // Create ProgramPoint objects
                        final ProgramPoint pointFrom = new ProgramPoint(programPointFromName, progPointFromArguments);
                        final ProgramPoint pointTo = new ProgramPoint(programPointToName, progPointToArguments);

                        // x>y; x>=y
                        final String relations = graphParts[1].replace("[", "").replace("]", "").trim();
                        String[] relationsSplitted = CommonOperations.trimStringArray(relations.split(","));
                        if (relations.length() == 0) {
                            relationsSplitted = new String[0];
                        }
                        // x>y => {x,y,>}
                        final String[][] relationsAsTriples = new String[relationsSplitted.length][];
                        for (int j = 0; j < relationsSplitted.length; j++) {
                            final String rel = relationsSplitted[j];
                            final String[] resRel = new String[3];
                            if (rel.indexOf(">=") >= 0) {
                                final String[] tmp = rel.split("(>=)");
                                resRel[0] = tmp[0];
                                resRel[1] = tmp[1];
                                resRel[2] = ">=";
                            } else if (rel.indexOf(">") >= 0) {
                                final String[] tmp = rel.split(">");
                                resRel[0] = tmp[0];
                                resRel[1] = tmp[1];
                                resRel[2] = ">";
                            } else if (rel.indexOf("=") >= 0) {
                                final String[] tmp = rel.split("=");
                                resRel[0] = tmp[0];
                                resRel[1] = tmp[1];
                                resRel[2] = "=";
                            } else {
                                throw new RuntimeException("Illegal relation: '" + rel + "'.");
                            }
                            relationsAsTriples[j] = resRel;
                        }
                        final MCGraph mcGraph = new MCGraph(pointFrom, pointTo, relationsAsTriples);
                        if (Config.MC_TRANSITIVE_CLOSURE) {
                            mcGraph.transitiveClosure();
                        }

                        if (this._biggestMCG == null
                            || (mcGraph.getNumOfEdges() > this._biggestMCG.getNumOfEdges())
                            || (mcGraph.getNumOfEdges() == this._biggestMCG.getNumOfEdges() && mcGraph.getNumOfVerticses() > this._biggestMCG.getNumOfVerticses())) {
                            this._biggestMCG = mcGraph;
                        }
                        if (this._biggestMCGNodes == null || mcGraph.getNumOfNodes() > this._biggestMCGNodes.getNumOfNodes()) {
                            this._biggestMCGNodes = mcGraph;
                        }
                        if (this._biggestMCGNodesPerProgramPoint == null
                            || mcGraph.getNumOfNodesPerProgramPoint() > this._biggestMCGNodesPerProgramPoint.getNumOfNodesPerProgramPoint()) {
                            this._biggestMCGNodesPerProgramPoint = mcGraph;
                        }
                        inputFileMCGraphs.add(mcGraph);
                        if (Config.LOG_READING_INPUT) {
                            Logger.write("Read MC Graph: " + mcGraph);
                        }
                    } // if not comment (starts with #)
                }
                line = br.readLine(); // read line possibly with few graphs
            } // while
        } catch (final FileNotFoundException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        } catch (final IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }

        if (Config.MERGE_GRAPHS && Config.GRAPHICS) {
            new Swing(inputFileMCGraphs);
        }

        //D
        List<MCGraph> programMCGraphs = inputFileMCGraphs;
        if (Config.MERGE_GRAPHS) {
            programMCGraphs = this.mergeGraphs(inputFileMCGraphs);
        }

        //add mcgs to current program
        for (final MCGraph mcg : programMCGraphs) {
            this.addMCGraph(mcg);
        }

        this._initialMCGraphsList = this.getMCGraphs();
        if (Config.GRAPHICS) {
            new Swing(new ArrayList<MCGraph>(this._mcGraphs.values()));
        }
    }

    private Program() {
    }

    private Program(final List<MCGraph> inputMCGraphs) {
        for (final MCGraph mcGraph : inputMCGraphs) {
            if (this._biggestMCG == null
                || (mcGraph.getNumOfEdges() > this._biggestMCG.getNumOfEdges())
                || (mcGraph.getNumOfEdges() == this._biggestMCG.getNumOfEdges() && mcGraph.getNumOfVerticses() > this._biggestMCG.getNumOfVerticses())) {
                this._biggestMCG = mcGraph;
            }
            if (this._biggestMCGNodes == null || mcGraph.getNumOfNodes() > this._biggestMCGNodes.getNumOfNodes()) {
                this._biggestMCGNodes = mcGraph;
            }
            if (this._biggestMCGNodesPerProgramPoint == null
                || mcGraph.getNumOfNodesPerProgramPoint() > this._biggestMCGNodesPerProgramPoint.getNumOfNodesPerProgramPoint()) {
                this._biggestMCGNodesPerProgramPoint = mcGraph;
            }

            this.addMCGraph(mcGraph);
        }
        this._initialMCGraphsList = this.getMCGraphs();
    }

    public static Program create(final String inputFile) {
        try {
            final InputStream fis = new FileInputStream(inputFile);
            final InputStreamReader isr = new InputStreamReader(fis);
            final BufferedReader br = new BufferedReader(isr);
            return Program.create(br);
        } catch (final IOException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

    public static Program create(final BufferedReader inputReader) {
        return new Program(inputReader);
    }

    public static Program create() {
        return new Program();
    }

    public static Program create(final List<MCGraph> inputMCGraphs) {
        return new Program(inputMCGraphs);
    }

    // create Program from each SCC of the current one
    public List<Program> getSCCPrograms() {
        final List<Program> res = new ArrayList<Program>();
        final SCCGraph sccGraph = this.createSCCGraph();
        final List<List<String>> scComponents = sccGraph.getSCCComponents();
        for (final List<String> currentComponent : scComponents) {
            final List<MCGraph> currentComponentMCGraphs = this.getMCGraphs(currentComponent);

            // no edges in the xcurrent component (single point component)
            if (!currentComponentMCGraphs.isEmpty()) {
                final Program subProg = new Program(currentComponentMCGraphs);
                res.add(subProg);
            }
        }
        return res;
    }

    // ==================================== Create SCC ==========================================
    // return the IDs of all program points
    private String[] getProgramPointsIDs() {
        // store the IDs in resSet
        final Set<String> resSet = new HashSet<String>();
        for (final ProgramPoint programPoint : this.getProgramPoints()) {
            resSet.add(programPoint.getID());
        }

        // Set<String> to String[]
        final String[] res = new String[resSet.size()];
        int i = 0;
        for (final String string : resSet) {
            res[i] = string;
            i++;
        }
        return res;
    }

    // returns programPointID neighbours IDs
    private String[] getProgramPointNeighboursIDs(final String programPointID) {
        // find and store the nieghbour IDs in resSet
        final Set<String> resSet = new HashSet<String>();
        for (final MCGraph mcGraph : this.getMCGraphs()) {
            final String fromPointID = mcGraph.getPointFrom().getID();
            if (fromPointID.equals(programPointID)) {
                final String toPointID = mcGraph.getPointTo().getID();
                resSet.add(toPointID);
            }
        }

        // Set<String> to String[]
        final String[] res = new String[resSet.size()];
        int i = 0;
        for (final String string : resSet) {
            res[i] = string;
            i++;
        }
        return res;
    }

    public SCCGraph createSCCGraph() {
        if (Config.LOG_BUILDING_SCC) {
            Logger.writeReport("\n===================== Creating SCC graph. ====================");
        }

        final Hashtable<String, String[]> vertexesNeighbouring = new Hashtable<String, String[]>();

        // build program points IDs neighbouring vertexesNeighbouring
        // key: program point id
        // value: id-s of neighbours
        final String[] programPoitsIDs = this.getProgramPointsIDs();
        for (final String programPoitsID : programPoitsIDs) {
            final String[] neighbours = this.getProgramPointNeighboursIDs(programPoitsID);
            vertexesNeighbouring.put(programPoitsID, neighbours);
        }

        if (Config.LOG_BUILDING_SCC) {
            Logger.write("ProgramPoints: " + Arrays.toString(programPoitsIDs));
            Logger.write("MC Graphs" + this._mcGraphs.keySet().toString());
        }

        // build SCC graph and return list of components,
        // each component is a list of program points id-s
        final SCCGraph sccGraph = new SCCGraph(vertexesNeighbouring);

        // print the components
        if (Config.LOG_BUILDING_SCC) {
            final List<List<String>> scComponents = sccGraph.getSCCComponents();
            for (final List<String> currentComponent : scComponents) {
                final List<MCGraph> currentComponentMCGraphs = this.getMCGraphs(currentComponent);
                final List<String> mcGraphsIDs = new ArrayList<String>();
                for (final MCGraph mcGraph : currentComponentMCGraphs) {
                    mcGraphsIDs.add(mcGraph.getID());
                }
                Logger.writeReport("SCC: " + Arrays.toString(currentComponent.toArray()) + " " + mcGraphsIDs);
            }
        }

        return sccGraph;
    }

    // =============================== Level Mappings ===================================
    // - searches for LevelMapping which orients SCC defined by mcGrtaphs
    // - if failed to orient return null
    private LevelMapping findSCCLevelMapping(final List<MCGraph> mcGraphs) {
        this._timer.startNextSum(); //find ordering

        LevelMapping levelMapping = null;
        String[] solution = null;
        boolean withTags = false; // true iff used Tagged Level Mapping

        // find number of bits needed to represent tags
        int numOfProgPoints = 0;
        int numOfProgPointsArguments = 0;
        final Set<String> programPointsIDs = new HashSet<String>();
        for (final MCGraph mcg : mcGraphs) {
            if (!programPointsIDs.contains(mcg.getPointFrom().getID())) {
                programPointsIDs.add(mcg.getPointFrom().getID());
                numOfProgPoints++;
                numOfProgPointsArguments += mcg.getPointFrom().getArguments().length;
            }
            if (!programPointsIDs.contains(mcg.getPointTo().getID())) {
                programPointsIDs.add(mcg.getPointTo().getID());
                numOfProgPoints++;
                numOfProgPointsArguments += mcg.getPointTo().getArguments().length;
            }
        }
        int tagBitsNum = -1;
        int progPointsNumberingBitsNum = -1;
        switch (Config.NUMBERS_ENCODING) {
        case UNARY:
            tagBitsNum = numOfProgPointsArguments;
            progPointsNumberingBitsNum = numOfProgPoints;
            break;
        case BINARY:
            tagBitsNum = CommonOperations.numOfBits(numOfProgPointsArguments);
            progPointsNumberingBitsNum = CommonOperations.numOfBits(numOfProgPoints);
            break;
        default:
            throw new RuntimeException("Illegal tags type: " + Config.NUMBERS_ENCODING + ".");
        }

        if (Config.LOG_LEVEL_MAPPINGS_SEARCH) {
            Logger.write("Tags representation: " + Config.NUMBERS_ENCODING + "; Bits per tag: " + tagBitsNum + ".");
        }

        // ============= Find level mapping for mcGraphs list =================

        // try to orient graphs using level mapping:
        // max without tags

        // list of ordering types. Try to order graphs using these odering types. If failed i try i+1.
        final String[] orderingTypes = Config.GRAPHS_ORDERING_TYPES;
        boolean success = false; //ordered graphs
        String orderingType = null; //ordering type if succeed to order graphs

        // ---------- loop over ordering types --------------
        for (int i = 0; !success && i < orderingTypes.length; i++) {
            orderingType = orderingTypes[i];

            SatEncoder enc = null;
            SatFormula formula = null;
            boolean isSolvable = false;

            this._timer.startNextSum(); //find ordering withTags+withoutTags
            if (Config.TRY_PLAIN_LEVEL_MAPPING) {
                withTags = false;
                if (Config.LOG_LEVEL_MAPPINGS_SEARCH) {
                    Logger.write("Searching Leval Mapping: type=" + orderingType + "; tagged=" + withTags + ".");
                }

                if (Config.CALL_GC) {
                    System.gc();
                }

                this._timer.startNext();
                enc = new SatEncoder(orderingType, withTags, tagBitsNum, progPointsNumberingBitsNum);
                formula = enc.encodeProgram(mcGraphs, orderingType, withTags, tagBitsNum); // without tags

                // run SAT Solver
                isSolvable = formula.isSolvable();
                if (Config.LOG_TIMES) {
                    Logger.write("Time (one type not tagged level mapping): " + this._timer.endCurrent() + " seconds "
                        + "[Ordering=" + orderingType + "; Tags=" + withTags + "].");
                }
            }
            if (Config.TRY_PLAIN_LEVEL_MAPPING && isSolvable) { // succeeded to orient using max without tags
                if (Config.LOG_LEVEL_MAPPINGS_SEARCH) {
                    Logger.write("Found Leval Mapping: type=" + orderingType + "; tagged=" + withTags + ".");
                }
                success = true;
                solution = formula.getSolution();
                levelMapping = new LevelMapping(orderingType);
            } else { // failed to orient using max without tags
                // try to orient the graphs using level mappinmg:
                // max with tags
                withTags = true;
                if (Config.LOG_LEVEL_MAPPINGS_SEARCH) {
                    Logger.write("Searching Laval Mapping: type=" + orderingType + "; tagged=" + withTags);
                }

                if (Config.CALL_GC) {
                    System.gc();
                }

                this._timer.startNext();
                enc = new SatEncoder(orderingType, withTags, tagBitsNum, progPointsNumberingBitsNum);
                formula = enc.encodeProgram(mcGraphs, orderingType, withTags, tagBitsNum); // with tags

                // run SAT Solver
                isSolvable = formula.isSolvable();
                if (Config.LOG_TIMES) {
                    Logger.write("Time (one type tagged level mapping): " + this._timer.endCurrent() + " seconds "
                        + "[Ordering=" + orderingType + "; Tags=" + withTags + "].");
                }

                if (isSolvable) { // succeeded to orient using max with tags
                    success = true;
                    if (Config.LOG_LEVEL_MAPPINGS_SEARCH) {
                        Logger.write("Found Leval Mapping: type=" + orderingType + "; tagged=" + withTags + ".");
                    }
                    solution = formula.getSolution();
                    levelMapping = new TaggedLevelMapping(orderingType);
                } else { // failed to orient using max without tags
                    if (Config.LOG_LEVEL_MAPPINGS_SEARCH) {
                        Logger.write("No Leval Mapping found using ordering: " + orderingType + ".");
                    }
                }
                if (Config.LOG_TIMES) {
                    Logger.writeReport("Time (" + orderingType + " ordering): "
                        + Timer.printTime(this._timer.endCurrent()) + ".");
                }
            }

        } //for - loop over ordering types

        if (Config.LOG_TIMES) {
            Logger.writeReport("Time (one level mapping): " + Timer.printTime(this._timer.endCurrent()) + ".");
        }

        // all opdering failed
        if (!success) {
            if (Config.LOG_LEVEL_MAPPINGS_RESULT) {
                Logger.writeReport("++++++++++++++++++++ No Leval Mapping found! ++++++++++++++++++++");
            }
            this._mcGraphsMappings = null;
            if (Config.GRAPHICS) {
                new Swing(mcGraphs);
            }
            return null;
        }

        // ================== Handle the result =============
        final Set<String> solutionSet = new HashSet<String>(Arrays.asList(solution));

        // handle vertexes coverage
        for (final MCGraph mcGraph : mcGraphs) {
            final Argument[] argsFrom = mcGraph.getPointFrom().getArguments();
            final Argument[] argsTo = mcGraph.getPointTo().getArguments();

            final String[] directionsTitles = {"Top->Bottom", "Bottom->Top", "Top->Top", "Bottom->Bottom" };
            final String[] directions =
                {Constants.TOP_TO_BOTTOM, Constants.BOTTOM_TO_TOP, Constants.TOP_TO_TOP, Constants.BOTTOM_TO_BOTTOM };
            final Argument[][] argsFromList = {argsFrom, argsTo, argsFrom, argsTo };
            final Argument[][] argsToList = {argsTo, argsFrom, argsFrom, argsTo };

            final String[] toPrint = new String[directions.length];

            for (int directionNum = 0; directionNum < directions.length; directionNum++) {
                toPrint[directionNum] = "\t" + directionsTitles[directionNum] + ": ";

                //ms coverages
                for (int fromArgInd = 0; fromArgInd < argsFromList[directionNum].length; fromArgInd++) {
                    for (int toArgInd = 0; toArgInd < argsToList[directionNum].length; toArgInd++) {
                        final String coveringVar =
                            SatEncoder.coveredByVar(mcGraph.getID(), fromArgInd, toArgInd, directions[directionNum]);
                        if (solutionSet.contains(coveringVar)) {
                            levelMapping.addVertexCoverage(toArgInd, fromArgInd, mcGraph.getID(),
                                directions[directionNum]);
                            final String coveringTypeVar =
                                SatEncoder.weaklyCoversVar(mcGraph.getID(), fromArgInd, directions[directionNum]);
                            if (solutionSet.contains(coveringTypeVar)) {
                                toPrint[directionNum] += fromArgInd + "->" + toArgInd + ", ";
                            } else {
                                // strictly
                                toPrint[directionNum] += fromArgInd + "=>" + toArgInd + ", ";
                            }
                        }
                    }
                }

                //dms coverages
                for (int toArgInd = 0; toArgInd < argsToList[directionNum].length; toArgInd++) {
                    for (int fromArgInd = 0; fromArgInd < argsFromList[directionNum].length; fromArgInd++) {
                        final String coveringVar =
                            SatEncoder.coveredByVar(mcGraph.getID(), toArgInd, fromArgInd, directions[directionNum]);
                        if (solutionSet.contains(coveringVar)) {
                            levelMapping.addVertexCoverage(fromArgInd, toArgInd, mcGraph.getID(),
                                directions[directionNum]);

                            final String coveringTypeVar =
                                SatEncoder.weaklyCoversVar(mcGraph.getID(), toArgInd, directions[directionNum]);
                            if (solutionSet.contains(coveringTypeVar)) {
                                toPrint[directionNum] += toArgInd + "->" + fromArgInd + ", ";
                            } else {
                                // strictly
                                toPrint[directionNum] += toArgInd + "=>" + fromArgInd + ", ";
                            }
                        }
                    }
                }
            }

            //            Logger.write("Args Coverage for: "+mcGraph.getID());
            //            for (int i=0; i<toPrint.length; i++)
            //                Logger.write(toPrint[i]);
        }

        // Handle program points result
        final Set<ProgramPoint> programPoints = this.getGraphsProgramPoints(mcGraphs);
        for (final ProgramPoint progPoint : programPoints) {
            final Argument[] arguments = progPoint.getArguments();

            // Handle arguments filtering
            final Set<Integer> filteredArgumentsHi = new HashSet<Integer>();
            final Set<Integer> filteredArgumentsLo = new HashSet<Integer>();
            for (int i = 0; i < arguments.length; i++) {
                final String varNameHi = SatEncoder.progPointArgToVar(progPoint.getID(), i, Constants.HighLow.HIGH);
                if (solutionSet.contains(varNameHi)) {
                    filteredArgumentsHi.add(i);
                }
                final String varNameLo = SatEncoder.progPointArgToVar(progPoint.getID(), i, Constants.HighLow.LOW);
                if (solutionSet.contains(varNameLo)) {
                    filteredArgumentsLo.add(i);
                }
            }
            levelMapping.addProgramPoint(progPoint.getID(), filteredArgumentsHi, filteredArgumentsLo);

            // Handle tags - for Tagged Level Mapping
            if (withTags) {
                final int numOfArgs = progPoint.getArguments().length;

                for (int i = 0; i < numOfArgs; i++) {
                    final int[] tagAsBitsArray = new int[tagBitsNum];
                    for (int j = 0; j < tagBitsNum; j++) {
                        final String argTagVar = SatEncoder.progPointArgTagVar(progPoint.getID(), i, j);
                        if (solutionSet.contains(argTagVar)) {
                            tagAsBitsArray[j] = 1;
                        } else if (solutionSet.contains(CommonOperations.negateLiteral(argTagVar))) {
                            tagAsBitsArray[j] = 0;
                        } else {
                            tagAsBitsArray[j] = 0;
                        }
                    }
                    int tag = -1;
                    switch (Config.NUMBERS_ENCODING) {
                    case UNARY:
                        tag = CommonOperations.unaryToDecimal(tagAsBitsArray);
                        break;
                    case BINARY:
                        tag = CommonOperations.binaryToDecimal(tagAsBitsArray);
                        break;
                    default:
                        throw new RuntimeException("Illegal tags type: " + Config.NUMBERS_ENCODING + ".");
                    }
                    ((TaggedLevelMapping) levelMapping).addTag(progPoint.getID(), i, tag);
                }
            }
        }

        for (final ProgramPoint programPoint : programPoints) {
            final String progPointID = programPoint.getID();
            final int[] progPointBoundNumberingVars = new int[progPointsNumberingBitsNum];
            final int[] progPointStrictNumberingVars = new int[progPointsNumberingBitsNum];
            for (int i = 0; i < progPointsNumberingBitsNum; i++) {
                final String varNameBound = SatEncoder.progPointBoundNumberVar(progPointID, i);
                if (solutionSet.contains(varNameBound)) {
                    progPointBoundNumberingVars[i] = 1;
                } else if (solutionSet.contains(CommonOperations.negateLiteral(varNameBound))) {
                    progPointBoundNumberingVars[i] = 0;
                }

                final String varNameStrict = SatEncoder.progPointStrictNumberVar(progPointID, i);
                if (solutionSet.contains(varNameStrict)) {
                    progPointStrictNumberingVars[i] = 1;
                } else if (solutionSet.contains(CommonOperations.negateLiteral(varNameStrict))) {
                    progPointStrictNumberingVars[i] = 0;
                }
            }
            int boundNum = -1;
            int strictNum = -1;
            switch (Config.NUMBERS_ENCODING) {
            case UNARY:
                boundNum = CommonOperations.unaryToDecimal(progPointBoundNumberingVars);
                strictNum = CommonOperations.unaryToDecimal(progPointStrictNumberingVars);
                break;
            case BINARY:
                boundNum = CommonOperations.binaryToDecimal(progPointBoundNumberingVars);
                strictNum = CommonOperations.binaryToDecimal(progPointStrictNumberingVars);
                break;
            default:
                throw new RuntimeException("Illegal tags type: " + Config.NUMBERS_ENCODING + ".");
            }
            levelMapping.addProgPointBoundNumber(progPointID, boundNum);
            levelMapping.addProgPointStrictNumber(progPointID, strictNum);
        }

        // Handle MC Graphs results: weakly and strictly ordered updates
        for (final MCGraph currentMCGraph : mcGraphs) {
            final String weaklyOrderedVarName = SatEncoder.weakGraphOrderingVar(currentMCGraph.getID(), orderingType);
            final String strictlyOrderedVarName = SatEncoder.strictGraphOrderingVar(currentMCGraph.getID(), orderingType);
            final String inCutsetVarName = SatEncoder.cutsetGraphVar(currentMCGraph.getID(), orderingType);
            final String removableStrictlyOrderedVarName =
                SatEncoder.removableStrictGraphOrderingVar(currentMCGraph.getID(), orderingType);
            if (solutionSet.contains(strictlyOrderedVarName)) {
                levelMapping.strictGraphOrdering(currentMCGraph.getID());
            }
            if (solutionSet.contains(weaklyOrderedVarName)) {
                levelMapping.weakGraphOrdering(currentMCGraph.getID());
            }
            if (solutionSet.contains(inCutsetVarName)) {
                levelMapping.graphInCutset(currentMCGraph.getID());
            }
            if (solutionSet.contains(removableStrictlyOrderedVarName)) {
                levelMapping.strictRemovableGraphOrdering(currentMCGraph.getID());
            }
        }

        if (levelMapping != null) {
            this._mcGraphsMappings.add(levelMapping);
        }

        if (Config.GRAPHICS && levelMapping != null) {
            new Swing(mcGraphs, levelMapping);
        }

        return levelMapping;
    }

    // remove mcGraphs between different SCCs
    private void removeInterComponentGraphs(final List<List<String>> scComponents) {
        // List<List<String>> => List<Set<String>>
        final List<Set<String>> scComponentsSets = new ArrayList<Set<String>>();
        for (final List<String> component : scComponents) {
            scComponentsSets.add(new HashSet<String>(component));
        }

        final List<String> removeGraphsIDs = new ArrayList<String>();
        for (final String mcGraphID : this._mcGraphs.keySet()) {
            final MCGraph mcGraph = this._mcGraphs.get(mcGraphID);
            boolean innerMcGraph = false;
            for (final Iterator<Set<String>> compIt = scComponentsSets.iterator(); compIt.hasNext() && !innerMcGraph;) {
                final Set<String> compSet = compIt.next();
                if (compSet.contains(mcGraph.getPointFrom().getID()) && compSet.contains(mcGraph.getPointTo().getID())) {
                    innerMcGraph = true;
                }
            }

            if (!innerMcGraph) {
                if (Config.LOG_BUILDING_SCC) {
                    Logger.write("Removing inter-componential mc graph: " + mcGraph.getID());
                }
                removeGraphsIDs.add(mcGraph.getID());
            }
        }
        for (final String string : removeGraphsIDs) {
            this.removeMCGraph(string);
        }
    }

    public List<LevelMapping> findLevelMappings() {
        this._timer.startNextSum();

        final List<LevelMapping> res = new ArrayList<LevelMapping>();

        while (!this._mcGraphs.isEmpty()) {

            final SCCGraph sccGraph = this.createSCCGraph();
            final List<List<String>> scComponents = sccGraph.getSCCComponents();
            //        _sccComponents.add(scComponents); //save for future use (printing Ranking Function in the end)
            if (scComponents.size() > 1) {
                final NumericMapping numMap = new NumericMapping(scComponents);
                this._mcGraphsMappings.add(numMap);
                Logger.write(numMap.toString());
            }

            // remove graphs which points are in different components
            this.removeInterComponentGraphs(scComponents);

            final List<LevelMapping> iterationLevelMappings = new ArrayList<LevelMapping>();
            for (final List<String> currentComponent : scComponents) {
                final List<MCGraph> currentComponentMCGraphs = this.getMCGraphs(currentComponent);

                // no edges in the xcurrent component (single point component)
                if (currentComponentMCGraphs.isEmpty()) {
                    continue;
                }

                // list of MCGraphs to list of IDs
                final List<String> mcGraphsIDs = new ArrayList<String>();
                for (final MCGraph mcGraph : currentComponentMCGraphs) {
                    mcGraphsIDs.add(mcGraph.getID());
                }

                Logger.writeReport("\n======================================================================================\n"
                    + "Processing component: \n"
                    + "Program Points: "
                    + Arrays.toString(currentComponent.toArray())
                    + "\n"
                    + "MC Graphs: "
                    + mcGraphsIDs
                    + "\n"
                    + "======================================================================================");

                // Find level mapping
                final LevelMapping levelMapping = this.findSCCLevelMapping(currentComponentMCGraphs);

                // no level mapping found
                if (levelMapping == null) {
                    if (Config.LOG_TIMES) {
                        Logger.writeReport("Total time (failure): " + Timer.printTime(this._timer.endCurrent()) + ".");
                    }
                    return null;
                }

                iterationLevelMappings.add(levelMapping);

                // remove graphs
                for (final String string : levelMapping.getRemovableGraphs()) {
                    this.removeMCGraph(string);
                }

                // print the current component level mapping
                if (Config.LOG_LEVEL_MAPPINGS_RESULT) {
                    Logger.writeReport("\n------------------------ Level Mapping -------------------------");
                    Logger.writeReport("Ordering strictly MC Graphs: "
                        + Arrays.toString(levelMapping.getStrictOrderedGraphs().toArray()) + " (type="
                        + levelMapping.getType() + ")");
                    Logger.write(levelMapping.toString());
                }
            }

            res.addAll(iterationLevelMappings);
        }

        if (Config.LOG_TIMES) {
            Logger.writeReport("Total time (success): " + Timer.printTime(this._timer.endCurrent()) + ".");
        }
        return res;
    }

    public List<MCGraphMapping> getMcGraphsMappings() {
        return this._mcGraphsMappings;
    }

    public MCGraph getBiggestMCG() {
        return this._biggestMCG;
    }

    public MCGraph getBiggestMCGNodes() {
        return this._biggestMCGNodes;
    }

    public MCGraph getBiggestMCGNodesPerProgramPoint() {
        return this._biggestMCGNodesPerProgramPoint;
    }

    /**
     * From Igor's original data structure to an immutable Obligation.
     * @return
     */
    public MCSProblem toMCSProblem() {
        final Set<MCRule> protoMCRules = new LinkedHashSet<MCRule>();
        for (final MCGraph mcGraph : this._mcGraphs.values()) {
            final MCRule mcRule = mcGraph.toMCRule();
            protoMCRules.add(mcRule);
        }
        final ImmutableSet<MCRule> mcRules = ImmutableCreator.create(protoMCRules);
        final MCSProblem res = MCSProblem.create(mcRules);
        return res;
    }

    /**
     * @param mcs
     * @return a corresponding program object
     */
    public static Program createFromMCSProblem(final MCSProblem mcs) {
        final Set<MCRule> mcRules = mcs.getRules();
        final List<MCGraph> mcGraphs = new ArrayList<MCGraph>(mcRules.size());
        for (final MCRule mcRule : mcRules) {
            final MCGraph mcGraph = MCGraph.createFromMCRule(mcRule);
            mcGraphs.add(mcGraph);
        }
        final Program res = Program.create(mcGraphs);
        return res;
    }
}
