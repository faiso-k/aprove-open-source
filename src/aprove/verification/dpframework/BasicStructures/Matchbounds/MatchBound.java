package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * <code>MatchBound</code> provides the basic functionality needed to
 * handle RFC MatchBounds. That includes the generations of the
 * required sets <em>R<sub>#</sub></em> and <em>match(R)</em>.
 *
 * @author <a href="mailto:chang@ariadne.informatik.rwth-aachen.de">Christian Hang</a>
 * @version $Id$
 */
public class MatchBound<X> {

    protected static Logger logger = Logger.getLogger("aprove.verification.oldframework.Rewriting.MatchBounds.MatchBound");

    private Node<X> startNode;
    private Node<X> sharpSink;
    private Set<List<EdgeEquality<AnnotatedFunctionSymbol, X>>> handledPaths;
    private CertificateGraph<X> certificate;
    private AnnotatedFunctionSymbol sharpLabel;
    private MatchingRulesState startState;
    private Set<Rule> rules;
    private Set<Rule> initRules;
    private PathFinder<X> pathFinder;
    private PathFinder<X> initPathFinder;
    private int maximalBound;
    private int maximalNodeBound;
    private int maximalEdgeBound;

    private MatchBound(final Set<Rule> origRules, final Set<FunctionSymbol> signatureOfRules, final Set<FunctionSymbol> fullSignature) {
        if (Globals.useAssertions) {
            assert(signatureOfRules.containsAll(CollectionUtils.getFunctionSymbols(origRules)));
        }
        this.rules = this.extendEmptyRhs(origRules, signatureOfRules);
        this.initRules = this.rules;
        this.handledPaths = new LinkedHashSet<List<EdgeEquality<AnnotatedFunctionSymbol, X>>>();

        this.pathFinder = new ZantemaImprovedPathFinder<X>();
        this.initPathFinder = new ZantemaImprovedPathFinder<X>();
        this.maximalBound = 0;
        this.maximalNodeBound = 250;
        this.maximalEdgeBound = 300;

        this.createSharpSymbol(fullSignature);

        this.certificate = new CertificateGraph<X>();
        this.startNode = new Node<X>();
        this.certificate.addNode(this.startNode);
        this.sharpSink = new Node<X>();
        this.certificate.addNode(this.sharpSink);
        this.certificate.setStartNode(this.startNode);
        this.certificate.setSharpSink(this.sharpSink);
        this.certificate.addEdge(this.sharpSink, this.sharpSink, this.sharpLabel);

        final Set<Rule> sharpRules = this.createRSharp(this.rules);

        if (Globals.DEBUG_COTTO) {
            if (MatchBound.logger.isLoggable(Level.FINE)) {
                MatchBound.logger.log(Level.FINE, "Using the following #-rules:\n");
                for (final Rule sharpRule : sharpRules) {
                    MatchBound.logger.log(Level.FINE, "{0}\n", sharpRule);
                }
            }
        }

        this.startState = MatchingRulesState.constructFromRules(sharpRules);

    }

    private MatchBound(final Set<Rule> initRules, final Set<Rule> rules,
            final Set<FunctionSymbol> signatureOfRules,
            final Set<FunctionSymbol> fullSignature) {
        this(rules, signatureOfRules, fullSignature);

        this.initRules = this.extendEmptyRhs(initRules, signatureOfRules);

        // the initial rules must be a subset of rules

        if (Globals.useAssertions) {
           rules.containsAll(initRules);
        }

    }

    public MatchBound(final Set<Rule> initRules, final Set<Rule> rules, final Set<FunctionSymbol> signatureOfRules, final Set<FunctionSymbol> fullSignature, final int nodeBound, final int edgeBound) {

        this(initRules, rules, signatureOfRules, fullSignature);
        this.maximalNodeBound = nodeBound;
        this.maximalEdgeBound = edgeBound;

    }

    public MatchBound(final Set<Rule> rules, final Set<FunctionSymbol> signatureOfRules, final Set<FunctionSymbol> fullSignature, final int nodeBound, final int edgeBound) {

        this(rules, signatureOfRules, fullSignature);
        this.maximalNodeBound = nodeBound;
        this.maximalEdgeBound = edgeBound;

    }

    private void createSharpSymbol(final Set<FunctionSymbol> signature) {

        final String name = "#";
        final int arity = 1;
        FunctionSymbol sharp = FunctionSymbol.create(name, arity);
        int nr = 1;
        while (signature.contains(sharp)) {
            sharp = FunctionSymbol.create(name+nr, arity);
            nr++;
        }

        this.sharpLabel = new AnnotatedFunctionSymbol(sharp, 0);
    }

    /*
     * precalculation of [] and [x] as argument-vectors
     */

    private static final ImmutableArrayList<TRSTerm> varArgs;
    private static final ImmutableArrayList<TRSTerm> zeroArgs;
    static {
        ArrayList<TRSTerm> tmpArgs = new ArrayList<TRSTerm>(1);
        tmpArgs.add(TRSTerm.createVariable("x"));
        varArgs = ImmutableCreator.create(tmpArgs);
        tmpArgs = new ArrayList<TRSTerm>(0);
        zeroArgs = ImmutableCreator.create(tmpArgs);
    }

    private Set<Rule> extendEmptyRhs(final Set<Rule> inputRules, final Set<FunctionSymbol> signature) {
        /*
         * the resulting set of rules
         */
        final Set<Rule> checkedRules = new LinkedHashSet<Rule>();

        for (Rule rule : inputRules) {

            final TRSTerm rhs = rule.getRight();

            // Check here, if we have to deal with an empty right-hand side
            if (rhs.isVariable()) {
                if (Globals.DEBUG_COTTO) {
                    MatchBound.logger.log(Level.FINEST, "Extending {0}\n", rule);
                }
                final TRSFunctionApplication lhs = rule.getLeft();
                final TRSVariable var = (TRSVariable) rhs;
                // then substitute x by all function-symbol-terms
                for (final FunctionSymbol f : signature) {
                    if (Globals.DEBUG_COTTO) {
                        MatchBound.logger.log(Level.FINEST, "Extending with symbol {0}\n", f);
                    }

                    final ImmutableArrayList<TRSTerm> args = f.getArity() == 0 ? MatchBound.zeroArgs : MatchBound.varArgs;
                    final TRSTerm newRhs = TRSTerm.createFunctionApplication(f, args);
                    final TRSFunctionApplication newLhs = lhs.applySubstitution(TRSSubstitution.create(var, newRhs));

                    rule = Rule.create(newLhs, newRhs);
                    if (Globals.DEBUG_COTTO) {
                        MatchBound.logger.log(Level.FINEST, "Adding rule {0}\n", rule);
                    }
                    checkedRules.add(rule);

                }
            } else {
                checkedRules.add(rule);
            }

        }

        return checkedRules;

    }

    /**
     * Gets the set of <em>R<sub>#</sub></em> rules for some specified
     * rules.
     *
     * @param inputRules a <code>Set<Rule></code> for which
     * <em>R<sub>#</sub></em> should be constructed
     * @return a <code>Set<Rule></code> value
     */
    public Set<Rule> createRSharp(final Set<Rule> inputRules) {

        final Set<Rule> sharpRules = new LinkedHashSet<Rule>();

        final SharpCutter cutter = new SharpCutter(this.sharpLabel.f);

        for (final Rule rule : inputRules) {

            final TRSFunctionApplication lhs = rule.getLeft();
            final TRSTerm rhs = rule.getRight();

            sharpRules.add(rule);

            int depthCounter = 0;
            TRSTerm tmpTerm = lhs;
            while (!tmpTerm.isVariable()) {
                final TRSFunctionApplication fTerm = (TRSFunctionApplication) tmpTerm;
                depthCounter++;
                if (fTerm.getRootSymbol().getArity() == 0) {
                    break;
                }
                tmpTerm = fTerm.getArgument(0);
            }

            for (int depth = depthCounter-1; depth > 0; depth--) {
                final Rule newRule = Rule.create(cutter.cut(lhs, depth), rhs);
                if (Globals.DEBUG_COTTO) {
                    MatchBound.logger.log(Level.FINEST, "Adding #-rule: {0}\n", newRule);
                }
                sharpRules.add(newRule);
            }

        }

        return sharpRules;

    }

    /**
     * Gets a pretty <code>String</code>, representing a specified
     * path in the graph. This method is used for loggin output.
     *
     * @param path a <code>List<Edge></code>, defining a path
     * @return a <code>String</code>, representing the path
     */
    public static <X> String pathToString(final List<EdgeEquality<AnnotatedFunctionSymbol, X>> path) {

        String out = "";
        boolean first = true;

        for (final EdgeEquality<AnnotatedFunctionSymbol, X> edge : path) {
            if (first) {
                first = false;
                out += "[" + edge.getStartNode().getNodeNumber() + "]";
            }

            out += " -" /*+ edge.getEdgeNumber() + "|"*/ + edge.getObject() + "-> ";
            out += "[" + edge.getEndNode().getNodeNumber() + "]";

        }

        return out;

    }

    /**
     * Get all paths in the graph, that match a left hand side of a
     * rule in <em>R<sub>#</sub></em>, including those matching rules.
     *
     * @return a <code>Set</code> of {@link MatchCollector
     * MatchCollector}s, each one defining paths in the graph it's
     * matching rules.
     */
    private Set<MatchCollector<X>> getMatchingPaths(final Abortion aborter) throws AbortionException {
        final Set<MatchCollector<X>> matchesFound = new LinkedHashSet<MatchCollector<X>>();
        Map<EdgeEquality<AnnotatedFunctionSymbol, X>, Set<MatchCollector<X>>> possibleMatches = new LinkedHashMap<EdgeEquality<AnnotatedFunctionSymbol, X>, Set<MatchCollector<X>>>();

        if (Globals.DEBUG_COTTO) {
            MatchBound.logger.log(Level.FINER, "Starting to determine matching paths in graph\n");
        }

        //logger.log(Level.FINEST, this.certificate.prettyToString());

        // Fill the set of possible matches initially with all edges
        // of the graph, that could be the start for a matching path

        for (final EdgeEquality<AnnotatedFunctionSymbol, X> edge : this.certificate.getEdges()) {
            for (final AnnotatedFunctionSymbol annSymbol : edge.getObject()) {
                final FunctionSymbol symbol = annSymbol.f;
                final MatchingRulesState successor = this.startState.getSuccessor(symbol);
                if (successor != null) {
                    // there is a rule that starts with this symbol
                    final List<EdgeEquality<AnnotatedFunctionSymbol, X>> startPath = new ArrayList<EdgeEquality<AnnotatedFunctionSymbol, X>>();

                    final EdgeEquality<AnnotatedFunctionSymbol, X> edge2 = new EdgeEquality<AnnotatedFunctionSymbol, X>(edge.getStartNode(), edge.getEndNode(), annSymbol);
                    startPath.add(edge2);

                    final Set<MatchCollector<X>> collectors = new LinkedHashSet<MatchCollector<X>>();
                    collectors.add(new MatchCollector<X>(startPath, successor, edge.getStartNode()));
                    possibleMatches.put(edge2, collectors);
                }
            }
        }

        // As long as we have possible matches, loop
        int counter = 0;
        while (!possibleMatches.isEmpty()) {

            final Map<EdgeEquality<AnnotatedFunctionSymbol, X>, Set<MatchCollector<X>>> newMap = new LinkedHashMap<EdgeEquality<AnnotatedFunctionSymbol, X>, Set<MatchCollector<X>>>();
            if (Globals.DEBUG_COTTO) {
                MatchBound.logger.log(Level.FINEST, "---- Starting new loop ----\n");
                // logger.log(Level.INFO, "size: " + this.certificate.getNodes().size() + " / " + this.certificate.getEdges().size());
            }

            // Iterate over every start-edge, that has possible
            // matches to examine

            for (final Map.Entry<EdgeEquality<AnnotatedFunctionSymbol, X>, Set<MatchCollector<X>>> entry : possibleMatches.entrySet()) {
                counter++;
                if ((counter & 0x20) == 0x20) {
                    counter = 0;
                    aborter.checkAbortion();
                }
                // Iterate over every branch, which runs through the
                // current edge.

                final EdgeEquality<AnnotatedFunctionSymbol, X> currentEdge = entry.getKey();
                if (Globals.DEBUG_COTTO) {
                    if (MatchBound.logger.isLoggable(Level.FINEST)) {
                        MatchBound.logger.log(Level.FINEST, "Now Handling Edge: " + currentEdge + "\n");
                    }
                }

                for (final MatchCollector<X> oldCollector : entry.getValue()) {

                    // For every edge leaving the end node of the
                    // current path, check if there exists a valid
                    // extension of it's path with that edge
                    if (Globals.DEBUG_COTTO) {
                        MatchBound.logger.log(Level.FINEST, "Following collector found: " /* + System.identityHashCode(oldCollector) + " " */ + oldCollector + "\n");
                    }

                    // Check if we found a match

                    if (oldCollector.getState().hasRules()) {
                        // found a path matching to a rule, rhs has to be added to the graph
                        oldCollector.setEndNode(currentEdge.getEndNode());
                        if (!this.handledPaths.contains(oldCollector.getPath())) {
                            // path has not been added yet, so we'll mark that for later
                            if (Globals.DEBUG_COTTO) {
                                if (MatchBound.logger.isLoggable(Level.FINER)) {
                                    MatchBound.logger.log(Level.FINER, "   Match found for path: " + oldCollector.getPath() + "\n");
                                }
                            }
                            matchesFound.add(oldCollector);
                            final List<EdgeEquality<AnnotatedFunctionSymbol, X>> pathCopy = new ArrayList<EdgeEquality<AnnotatedFunctionSymbol, X>>(oldCollector.getPath());
                            this.handledPaths.add(pathCopy);
                        }

                    }

                    final MatchingRulesState currentState = oldCollector.getState();

                    final Node<X> currentNode = currentEdge.getEndNode();
                    for (final EdgeEquality<AnnotatedFunctionSymbol, X> tmpEdge : this.certificate.getOutEdges(currentNode)) {
                        for (final AnnotatedFunctionSymbol annSymbol : tmpEdge.getObject()) {
                            final FunctionSymbol symbol = annSymbol.f;
                            final MatchingRulesState newState = currentState.getSuccessor(symbol);

                            if (newState != null) {

                                final List<EdgeEquality<AnnotatedFunctionSymbol, X>> tmpPath = oldCollector.getPath();

                                final List<EdgeEquality<AnnotatedFunctionSymbol, X>> pathCopy = new ArrayList<EdgeEquality<AnnotatedFunctionSymbol, X>>(tmpPath);
                                final EdgeEquality<AnnotatedFunctionSymbol, X> tmpEdge2 = new EdgeEquality<AnnotatedFunctionSymbol, X>(tmpEdge.getStartNode(), tmpEdge.getEndNode(), annSymbol);
                                pathCopy.add(tmpEdge2);

                                final MatchCollector<X> newCollector = new MatchCollector<X>(pathCopy, newState, oldCollector.getStartNode());
                                if (Globals.DEBUG_COTTO) {
                                    if (MatchBound.logger.isLoggable(Level.FINEST)) {
                                        MatchBound.logger.log(Level.FINEST, "   Found extension to path: " + symbol + " " + System.identityHashCode(newCollector) + " " + newCollector + "\n");
                                    }
                                }

                                if (!newMap.containsKey(tmpEdge2)) {
                                    newMap.put(tmpEdge2, new LinkedHashSet<MatchCollector<X>>());
                                }

                                final Set<MatchCollector<X>> collection = newMap.get(tmpEdge2);
                                collection.add(newCollector);
                                //logger.log(Level.FINEST, "newMap: " + newMap + "\n");
                            }
                        }

                    }

                }

            }

            possibleMatches = newMap;
        }

        if (Globals.DEBUG_COTTO) {
            MatchBound.logger.log(Level.FINER, "Finished finding new matching paths\n");
        }

        return matchesFound;

    }

    /**
     * Construct the initial graph, by taking all right hand sides of
     * the initial <em>R</em> and adding them to the graph.
     *
     */
    private boolean initGraph() {
        for (final Rule rule : this.initRules) {

            TRSTerm tmpTerm = rule.getRight();

            if (Globals.useAssertions) {
                // should not happen, as we extendRhs before!
                assert(!tmpTerm.isVariable());
            }

            final List<AnnotatedFunctionSymbol> liftedTerm = new ArrayList<AnnotatedFunctionSymbol>();

            while (tmpTerm instanceof TRSFunctionApplication) {

                // Lift symbol to 0

                final TRSFunctionApplication f = (TRSFunctionApplication) tmpTerm;
                final FunctionSymbol symbol = f.getRootSymbol();
                final AnnotatedFunctionSymbol labSym = new AnnotatedFunctionSymbol(symbol, 0);
                liftedTerm.add(labSym);

                if (symbol.getArity() > 0) {
                    tmpTerm = f.getArgument(0);
                } else {
                    tmpTerm = null;
                }


            }

            this.initPathFinder.insertPath(this.certificate, this.startNode, this.sharpSink, liftedTerm);

        }

        return true;

    }

    /**
     * Gets the certificate, if it exists for this MatchBound problem.
     * @param aborter
     * @return a <code>Graph</code>, representing the certificate
     * @throws AbortionException
     */
    public CertificateGraph<X> getCertificate(final Abortion aborter) throws AbortionException {
        final boolean initiable = this.initGraph();
        if (!initiable) {
            return null;
        }

//        logger.log(Level.FINEST, this.certificate.prettyToString());

        if (Globals.DEBUG_COTTO) {
            if (MatchBound.logger.isLoggable(Level.FINEST)) {
                MatchBound.logger.log(Level.FINEST, this.certificate.toSaveDOTwithEdges());
            }
        }
        // Iterate over all paths, check the DFA for matches and collect them in a set.

        Set<MatchCollector<X>> matchesFound = this.getMatchingPaths(aborter);

        if (Globals.DEBUG_COTTO) {
            if (MatchBound.logger.isLoggable(Level.FINEST)) {
                MatchBound.logger.log(Level.FINEST, "matchesFound: " + matchesFound + "\n");
            }
        }

        while (!matchesFound.isEmpty()) {
            aborter.checkAbortion();
            /*
            Set<MatchCollector<X>> matchesFound_orig = matchesFound;
            matchesFound = new LinkedHashSet<MatchCollector<X>>();
            Iterator matchIterx = matchesFound_orig.iterator();

            while (matchIterx.hasNext()) {
                String best = "";
                MatchCollector besto = null;

                while (matchIterx.hasNext()) {
                    MatchCollector next = (MatchCollector) matchIterx.next();
                    String string = next.toString();
                    if (best.equals("") || string.compareTo(best) < 0)
                    {
                        best = new String(string);
                        besto = next;
                    }
                }
                logger.log(Level.FINE,"Adding (sorted): " + best + "\n");
                matchesFound.add(besto);
                matchesFound_orig.remove(besto);
                matchIterx = matchesFound_orig.iterator();
            }
            */
            if (Globals.DEBUG_COTTO) {
                if (MatchBound.logger.isLoggable(Level.FINE)) {
                    MatchBound.logger.log(Level.FINE,this.certificate.toSaveDOTwithEdges());
                }
            }

//            logger.log(Level.FINE, "Matches Found:\n");
            //
//            Iterator i = matchesFound.iterator();
//            while (i.hasNext()) {
//                logger.log(Level.FINE, i.next().toString() + "\n");
//            }

//            Set<Set<EdgeEquality<AnnotatedFunctionSymbol,X>>> insertedPaths = new LinkedHashSet<Set<EdgeEquality<AnnotatedFunctionSymbol,X>>>();

//            Iterator matchIter = matchesFound.iterator();
            for (final MatchCollector<X> collector : matchesFound) {

                for (final Rule matchingRule : collector.getState().getRules()) {

                    final List<AnnotatedFunctionSymbol> lifted = this.liftRightHandSide(collector.getPath(), matchingRule);

                    StringBuilder logoutput = new StringBuilder();
                    if (Globals.DEBUG_COTTO) {
                        if (MatchBound.logger.isLoggable(Level.FINER)) {
                            logoutput.append("Inserting path [");
                            logoutput.append(collector.getStartNode());
                            logoutput.append("] ");
                        }
                    }
                    boolean newBound = false;
                    for (final AnnotatedFunctionSymbol asym : lifted) {

                        final int annotation = asym.nr;
                        if (annotation > this.maximalBound) {
                            newBound = true;
                            this.maximalBound = annotation;
                        }
                        if (Globals.DEBUG_COTTO) {
                            if (MatchBound.logger.isLoggable(Level.FINER)) {
                                logoutput.append(asym.f);
                                logoutput.append('(');
                                logoutput.append(annotation);
                                logoutput.append(") ");
                            }
                        }
                    }
                    if (Globals.DEBUG_COTTO) {
                        if (MatchBound.logger.isLoggable(Level.FINER)) {
                            MatchBound.logger.log(Level.FINER, logoutput + "[" + collector.getEndNode() + "]\n");
                        }
                        if (MatchBound.logger.isLoggable(Level.FINE)) {
                            if (newBound) {
                                MatchBound.logger.log(Level.FINE, "Setting new MatchBound: " + this.maximalBound + "\n");
                            }
                        }
                    }

//                    insertedPaths.add(this.pathFinder.insertPath(this.certificate, collector.getStartNode(), collector.getEndNode(), lifted));
                    this.pathFinder.insertPath(this.certificate, collector.getStartNode(), collector.getEndNode(), lifted);

                }

            }

            if (this.certificate.getNodes().size() > this.maximalNodeBound
                || this.certificate.getEdges().size() > this.maximalEdgeBound) {
                break;
            }


//            System.err.println(this.certificate.toDOTMatchingInserted(matchesFound, insertedPaths));

            matchesFound = this.getMatchingPaths(aborter);
//          logger.log(Level.FINE,this.certificate.toSaveDOTwithEdges());
//          logger.log(Level.FINE,"Nodes: " + this.certificate.getNodes().size() + "\n");
//          logger.log(Level.FINE,"Edges: " + this.certificate.getEdges().size() + "\n");
        }
        if (matchesFound.isEmpty()) {
            if (Globals.DEBUG_COTTO) {
                if (MatchBound.logger.isLoggable(Level.FINER)) {
                    MatchBound.logger.log(Level.FINER, this.certificate.toSaveDOTwithEdges());
                    MatchBound.logger.log(Level.FINER, "SUCESS with " + this.certificate.getNodes().size() + " nodes and " + this.certificate.getEdges().size() + " edges\n");
                }
            }
            return this.certificate;
        }
        if (Globals.DEBUG_COTTO) {
            if (MatchBound.logger.isLoggable(Level.INFO)) {
                if (this.certificate.getNodes().size() > this.maximalNodeBound) {
                    MatchBound.logger.log(Level.INFO,
                        "RFC Match Bounds aborting, as more than "
                            + this.maximalNodeBound + " nodes in graph\n");
                } else if (this.certificate.getEdges().size() > this.maximalEdgeBound) {
                    MatchBound.logger.log(Level.INFO,
                        "RFC Match Bounds aborting, as more than "
                            + this.maximalEdgeBound + " edges in graph\n");
                }
            }
        }
        return null;

    }

    /**
     * Gets a list of function symbols, which are lifted to a
     * specified bound, originating from a rule.
     *
     * @param annotations a <code>List<Edge></code> value
     * @param rule a <code>Rule</code> value
     * @return a <code>List<AnnotatedFunctionSymbol></code> value
     */
    public List<AnnotatedFunctionSymbol> liftRightHandSide(final List<EdgeEquality<AnnotatedFunctionSymbol, X>> annotations, final Rule rule) {

        final List<AnnotatedFunctionSymbol> rhs = new ArrayList<AnnotatedFunctionSymbol>();
        int minimalAnnotation = Integer.MAX_VALUE;

        // Find the minimal annotations on the left side

        for (final EdgeEquality<AnnotatedFunctionSymbol, X> edge : annotations) {

            final Collection<AnnotatedFunctionSymbol> symbols =
                edge.getObject();
            assert (symbols.size() == 1);
            final AnnotatedFunctionSymbol symbol = symbols.iterator().next();
            final int annotation = symbol.nr;
            if (annotation < minimalAnnotation) {
                minimalAnnotation = annotation;
            }

        }

        final int newAnnotation = minimalAnnotation + 1;

        TRSTerm tmpTerm = rule.getRight();
        while (tmpTerm instanceof TRSFunctionApplication) {

            // Lift symbol

            final TRSFunctionApplication f = (TRSFunctionApplication) tmpTerm;
            final FunctionSymbol symbol = f.getRootSymbol();
            final AnnotatedFunctionSymbol labSym = new AnnotatedFunctionSymbol(symbol, newAnnotation);
            rhs.add(labSym);

            if (symbol.getArity() > 0) {
                tmpTerm = f.getArgument(0);
            } else {
                tmpTerm = null;
            }

        }

        return rhs;
    }

    /**
     * Gets the Match Bound of this problem.
     *
     * @return the Match Bound of this problem
     */
    public int getMatchBound() {

        return this.maximalBound;

    }

    protected static class MatchCollector<X> {

        private List<EdgeEquality<AnnotatedFunctionSymbol, X>> annotatedPath;
        private MatchingRulesState state;
        private Node<X> startNode;
        private Node<X> endNode;

        public MatchCollector(final MatchingRulesState state, final Node<X> startNode) {

            this(null, state, startNode);

        }

        public MatchCollector(final List<EdgeEquality<AnnotatedFunctionSymbol, X>> annotatedPath, final MatchingRulesState state, final Node<X> startNode) {

            if (annotatedPath == null) {
                this.annotatedPath = new ArrayList<EdgeEquality<AnnotatedFunctionSymbol, X>>();
            } else {
                this.annotatedPath = annotatedPath;
            }
            this.state = state;
            this.startNode = startNode;

        }

        public List<EdgeEquality<AnnotatedFunctionSymbol, X>> getPath() {
            return this.annotatedPath;
        }

        public Node<X> getEndNode() {
            return this.endNode;
        }

        public void setEndNode(final Node<X> endNode) {
            this.endNode = endNode;
        }

        public Node<X> getStartNode() {
            return this.startNode;
        }

        public MatchingRulesState getState() {
            return this.state;
        }

        @Override
        public String toString() {

            String s = "[ " + MatchBound.pathToString(this.annotatedPath);
            s += " matches rules: " + this.state.getRules();
            return s + "]";

        }

    }

}
