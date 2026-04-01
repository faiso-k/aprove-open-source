/*
 * Created on Jan 26, 2006
 */
package aprove.verification.dpframework.DPProblem;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Represents an Dependency Graph for an Equational TRS. AC and C Equations in rWtihE
 * and sharped AC and C Equations in eSharp are asserted.
 * @author stein
 * @version $Id$
 */

public class EDependencyGraph implements Immutable {

    protected static Logger logger = Logger.getLogger("aprove.verification.dpframework.DPProblem.EDependencyGraph");

    /*
     * real values
     */
    private final Graph<HasTermPair, Object> g;
    private final ETRSProblem rWithE;
    private final ImmutableSet<Equation> eSharp;

    /*
     * calculated values
     */
    private final Map<FunctionSymbol, ImmutableSet<Rule>> rAsMap; // a map from defined symbols to their rules
    private final Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsRAsMap; // the lhs are in standard representation!!
                                                                     // this is essential for tcap!
    private final Set<FunctionSymbol> defSymsOfR;
    private Set<Cycle<HasTermPair>> sccs; // the set of sccs of this graph, null if the graph itself is an SCC;
                                   // must be computed in the constructor
    private Boolean eSharpIsAnC; //true iff eSharp only contains equations looking like A and C equations converted to sharped rootsymbols

    /**
     * create Graph from scratch
     */
    private EDependencyGraph(final Set<Rule> P, final ImmutableSet<Equation> eSharp, final ETRSProblem rWithE) {
        if (Globals.useAssertions) {
            assert rWithE.checkACandAandC();
        }
        this.eSharp = eSharp;
        this.rWithE = rWithE;
        this.rAsMap = rWithE.getRuleMap();
        this.defSymsOfR = rWithE.getDefinedSymbolsOfR();
        this.eSharpIsAnC = null;
        if (Globals.useAssertions) {
            assert this.checkESharpIsAnC();
        }
        this.lhsRAsMap = GeneralizedRule.computeLhsOfRulesAsMapInStandardRepresentation(this.rAsMap);
        final Set<Node<HasTermPair>> nodes = new LinkedHashSet<>();
        for (final Rule dp : P) {
            nodes.add(new Node<>(dp));
        }
        if (Options.certifier.isCeta()) { // CeTA expects Esharp as part of graph
            for (Equation e : eSharp) {
                nodes.add(new Node<>(e));
            }
        }

        this.g = new Graph<>(nodes);

        // first do crude approximation on root symbols
        // (this check requires non-collapsing rules!)
        // (only check nodes in sccs in more detail!)
        final int n = nodes.size();
        Node<HasTermPair>[] nodeArr = new Node[n];
        nodeArr = nodes.toArray(nodeArr);
        for (int i = 0; i < n; i++) {
            final Node<HasTermPair> fromDP = nodeArr[i];
            final HasTermPair fromDPRule = fromDP.getObject();
            for (int j = i + 1; j < n; j++) {
                final Node<HasTermPair> toDP = nodeArr[j];
                final HasTermPair toDPRule = toDP.getObject();
                // standard direction
                if (this.calculateFastConnection(fromDPRule, toDPRule)) {
                    this.g.addEdge(fromDP, toDP);
                }
                // reverse direction
                if (this.calculateFastConnection(toDPRule, fromDPRule)) {
                    this.g.addEdge(toDP, fromDP);
                }
            }
            // and self-cycle
            if (this.calculateFastConnection(fromDPRule, fromDPRule)) {
                this.g.addEdge(fromDP, fromDP);
            }
        }

        this.computeSccs();
        //now do real edge check on precomputed sccs
        this.checkEdgesOnSccs();
    }

    /**
     * create graph where P is a subset of the nodes in superGraph
     * => we do not have to check edges again
     * @param P
     * @param superGraph
     */
    private EDependencyGraph(final Set<Node<HasTermPair>> P, final EDependencyGraph superGraph) {
        if (Globals.useAssertions) {
            assert superGraph.g.getNodes().containsAll(P) && superGraph.rWithE.checkACandAandC()
                && superGraph.checkESharpIsAnC();
        }
        this.g = superGraph.g.getSubGraph(P);
        this.defSymsOfR = superGraph.defSymsOfR;
        this.lhsRAsMap = superGraph.lhsRAsMap;
        this.rAsMap = superGraph.rAsMap;
        this.rWithE = superGraph.rWithE;
        this.eSharp = superGraph.eSharp;
        this.eSharpIsAnC = null;
        this.computeSccs();
    }

    /**
     * create graph where P is a subset of the nodes in superGraph and
     * the edges are guaranteed to be included in the superGraph,
     * i.e. only already existent edges may be deleted.
     * @param P
     * @param superGraph
     */
    private EDependencyGraph(final Set<Node<HasTermPair>> P, final ETRSProblem rWithE, final EDependencyGraph superGraph) {
        if (Globals.useAssertions) {
            assert superGraph.g.getNodes().containsAll(P) && superGraph.rWithE.checkACandAandC()
                && superGraph.checkESharpIsAnC();
        }
        this.rWithE = rWithE;
        this.eSharp = superGraph.eSharp;
        this.eSharpIsAnC = null;
        this.rAsMap = rWithE.getRuleMap();
        this.defSymsOfR = rWithE.getDefinedSymbolsOfR();
        this.lhsRAsMap = GeneralizedRule.computeLhsOfRulesAsMapInStandardRepresentation(this.rAsMap);

        //      create graph with corresponding node-set
        this.g = superGraph.g.getSubGraph(P);

        this.computeSccs();
        this.checkEdgesOnSccs();
    }

    public EDependencyGraph getSubGraph(final Set<Node<HasTermPair>> P) {
        return new EDependencyGraph(P, this);
    }

    public EDependencyGraph getSubGraphFromPRules(final Set<Rule> P) {        
        Set<HasTermPair> P1 = new HashSet<>(P);
        P1.addAll(this.getEsharp());
        final Set<Node<HasTermPair>> nodesForP = this.g.getNodesFromObjects(P1);
        return new EDependencyGraph(nodesForP, this);
    }

    /**
     * creates a graph where P is a subset of the nodes and we draw edges
     * according to a new rWithE (i.e. delete edges not needed anymore)
     */
    public EDependencyGraph getSubGraph(final Set<Rule> P, final ETRSProblem rWithE) {
        Set<HasTermPair> P1 = new HashSet<>(P);
        P1.addAll(this.getEsharp());
        final Set<Node<HasTermPair>> nodesForP = this.g.getNodesFromObjects(P1);
        return new EDependencyGraph(nodesForP, rWithE, this);
    }

    public static EDependencyGraph create(final Set<Rule> P, final ImmutableSet<Equation> eSharp, final ETRSProblem rWithE) {
        return new EDependencyGraph(P, eSharp, rWithE);
    }

    /**
     * only checks on outermost symbols
     */
    private boolean calculateFastConnection(final HasTermPair from, final HasTermPair to) {
        final TRSTerm t = from.getRight();
        if (t.isVariable()) {
            return true;
        } else {
            final FunctionSymbol f = ((TRSFunctionApplication) t).getRootSymbol();
            return f.equals(((TRSFunctionApplication) to.getLeft()).getRootSymbol()) || this.defSymsOfR.contains(f);
        }
    }

    /**
     * Computes a finer connection on edges on sccs and updates the sccs accordingly.
     * sccs must have been computed in advance!
     */
    private void checkEdgesOnSccs() {
        final List<Edge<?, HasTermPair>> edges = new ArrayList<>(this.g.getEdges());
        boolean changed = false;
        if (this.sccs == null) {
            for (final Edge<?, HasTermPair> e : edges) {
                final Node<HasTermPair> from = e.getStartNode();
                final Node<HasTermPair> to = e.getEndNode();
                if (!this.calculateConnection(from, to)) {
                    this.g.removeEdge(from, to);
                    changed = true;
                }
            }
        } else {
            final Map<Node<HasTermPair>, Cycle<HasTermPair>> nodeToScc = new HashMap<>(this.g.getNodes().size());
            for (final Cycle<HasTermPair> cycle : this.sccs) {
                for (final Node<HasTermPair> node : cycle) {
                    nodeToScc.put(node, cycle);
                }
            }

            for (final Edge<?, HasTermPair> e : edges) {
                final Node<HasTermPair> from = e.getStartNode();
                final Node<HasTermPair> to = e.getEndNode();
                final Cycle<HasTermPair> fromCycle = nodeToScc.get(from);
                if (fromCycle != null && fromCycle == nodeToScc.get(to) && !this.calculateConnection(from, to)) {
                    this.g.removeEdge(from, to);
                    changed = true;
                }
            }
        }

        if (changed) {
            this.computeSccs();
        }
    }

    /**
     * does the usual forward checks with TCapE
     */
    private boolean calculateConnection(final Node<HasTermPair> from, final Node<HasTermPair> to) {
        HasTermPair fromPair = from.getObject();
        HasTermPair toPair = to.getObject();
        //to get variable disjunctive terms use THIRD_STANDARD_PREFIX, cause in the StandardRepresentation STANDARD_PREFIX is used
        Rule s_to_t = Rule.create((TRSFunctionApplication) fromPair.getLeft(), fromPair.getRight()).getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
        final TRSTerm t = s_to_t.getRight();
        final TRSFunctionApplication u = Rule.create((TRSFunctionApplication) toPair.getLeft(), toPair.getRight()).getLhsInStandardRepresentation();
        if (Globals.DEBUG_STEIN) {
            EDependencyGraph.logger.log(Level.FINEST, "   Calculating connection between " + t.toString() + " and " + u.toString()
                + "\n");
        }
        //assert disjunctive variables
        if (Globals.useAssertions) {
            assert (Collections.disjoint(u.getVariables(), t.getVariables()));
        }

        //cap and ren of t. here the SECOND_STANDARD_PREFIX is taken for variables
        final TRSTerm cap_t = t.tcapE(this.lhsRAsMap, this.rWithE.getACandASymbols(), this.rWithE.getCSymbols());

        if (cap_t.isVariable()) {
            return true;
        }
        //cap_t is not a variable
        final TRSFunctionApplication ta = (TRSFunctionApplication) cap_t;

        if (this.rWithE.checkACandAandC() && this.checkESharpIsAnC()) {
            if (!ta.getRootSymbol().equals(u.getRootSymbol())) {
                return false;
            }
            // ta and u have same rootSymbol
            final FunctionSymbol F = ta.getRootSymbol();
            //look if we have an commutative/assocative F equation in eSharp
            Equation cEq = null;
            Equation aEq = null;
            for (final Equation e : this.eSharp) {
                if (((TRSFunctionApplication) e.getLeft()).getRootSymbol().equals(F)) {
                    if (e.getFunctionSymbols().size() == 1) {
                        if (Equation.createCEquation(F).equals(e)) {
                            cEq = e;
                        }
                    } else if (e.getFunctionSymbols().size() == 2) {
                        final Set<FunctionSymbol> fs = new HashSet<>(e.getFunctionSymbols());
                        fs.remove(F);
                        final FunctionSymbol f = fs.iterator().next();
                        if (Equation.createSharpedAEquation(F, f).equals(e)) {
                            aEq = e;
                        }
                    }
                }
            }
            // if we have an associative one
            if (aEq != null) {
                final Set<FunctionSymbol> fs = new HashSet<>(aEq.getFunctionSymbols());
                fs.remove(F);
                final FunctionSymbol f = fs.iterator().next();
                //replace all Fs by fs in ta,u,eSharp and
                //return ta' E \cup eSharp'-unifies u'
                final TRSFunctionApplication taUnSharped = ta.replaceAll(F, f);
                final TRSFunctionApplication uUnSharped = u.replaceAll(F, f);
                final Set<FunctionSymbol> ACandAsE = new HashSet<>(this.rWithE.getACandASymbols());
                final Set<FunctionSymbol> Cs = this.rWithE.getCSymbols();
                //Add the unsharped aEq and unsharped cEq
                //For now the unsharped cEq is always added, because we take
                //AC-Unification for A Equations without corresponding C Equations.
                ACandAsE.add(f);
                final Set<FunctionSymbol> ACs = ImmutableCreator.create(ACandAsE);
                if (this.rWithE.checkACandA()) {
                    if (!new GeneralAC(ACs).areTheoryUnifiable(taUnSharped, uUnSharped)) {
                        return false;
                    }
                    return true;
                } else {
                    if (!new GeneralACnC(ACs, Cs).areTheoryUnifiable(taUnSharped, uUnSharped)) {
                        return false;
                    }
                    return true;
                }

            } else if (cEq != null) {
                //if only cEq may be applicable add this one to E and return ta E'-unifies u
                //For now we also take AC-Unification for A Equations without corresponding C Equations.
                final Set<FunctionSymbol> ACs = this.rWithE.getACandASymbols();
                final Set<FunctionSymbol> CsE = new HashSet<>(this.rWithE.getCSymbols());
                CsE.add(F);
                final Set<FunctionSymbol> Cs = ImmutableCreator.create(CsE);
                if (!new GeneralACnC(ACs, Cs).areTheoryUnifiable(ta, u)) {
                    return false;
                }
                return true;
            } else {
                //if no eSharp Equation for F, return ta E-unifies u
                //For now we also take AC-Unification for A Equations without corresponding C Equations.
                final Set<FunctionSymbol> ACs = this.rWithE.getACandASymbols();
                final Set<FunctionSymbol> Cs = this.rWithE.getCSymbols();
                if (this.rWithE.checkACandA()) {
                    if (!new GeneralAC(ACs).areTheoryUnifiable(ta, u)) {
                        return false;
                    }
                } else {
                    if (!new GeneralACnC(ACs, Cs).areTheoryUnifiable(ta, u)) {
                        return false;
                    }
                }
                return true;
            }
        }

        if (Globals.useAssertions) {
            //inform, if we don't only have AC Equations or not all cases are taken care of already
            assert (false);
        }
        return true;
    }

    /**
     * returns true iff this.eSharp only contains equations looking like A and C equations converted to sharped rootsymbols,
     * e.g. only contains equations of the form F(x,f(y,z))==F(f(x,y),z) and F(x,y)==F(y,x)
     */
    private boolean checkESharpIsAnC() {
        if (this.eSharpIsAnC == null) {
            this.eSharpIsAnC = true;
            for (final Equation eq : this.eSharp) {
                if (eq.getLeft().isVariable() || eq.getRight().isVariable()) {
                    this.eSharpIsAnC = false;
                    break;
                }
                final FunctionSymbol F = ((TRSFunctionApplication) eq.getLeft()).getRootSymbol();
                if (!((TRSFunctionApplication) eq.getRight()).getRootSymbol().equals(F)) {
                    this.eSharpIsAnC = false;
                    break;
                }
                final Set<FunctionSymbol> fs = new HashSet<>(eq.getFunctionSymbols());
                fs.remove(F);
                if (fs.isEmpty()) {
                    //it must be a C equation
                    final Equation cEquation = Equation.createCEquation(F);
                    if (!eq.equals(cEquation)) {
                        this.eSharpIsAnC = false;
                        break;
                    }
                } else if (fs.size() == 1) {
                    //it must be a A equation
                    final FunctionSymbol f = fs.iterator().next();
                    final Equation aEquation = Equation.createSharpedAEquation(F, f);
                    if (!eq.equals(aEquation)) {
                        this.eSharpIsAnC = false;
                        break;
                    }

                } else {
                    //too many FunctionSymbols
                    this.eSharpIsAnC = false;
                    break;
                }
            }
        }

        return this.eSharpIsAnC;
    }

    private void computeSccs() {
        final Set<Cycle<HasTermPair>> sccs = this.g.getSCCs();
        if (sccs.size() == 1) {
            if (sccs.iterator().next().size() == this.g.getNodes().size()) {
                this.sccs = null;
                return;
            }
        }
        this.sccs = sccs;
    }

    public boolean isSCC() {
        return this.sccs == null;
    }

    public ImmutableSet<EDependencyGraph> getSubSCCs() {
        final Set<EDependencyGraph> subSccs = new LinkedHashSet<>();
        for (final Set<Node<HasTermPair>> scc : this.sccs) {
            subSccs.add(this.getSubGraph(scc));
        }
        return ImmutableCreator.create(subSccs);
    }

    public ImmutableSet<Rule> getP() {
        Set<Rule> P = new HashSet<>();
        for (HasTermPair rule : this.g.getNodeObjects()) {
            if (rule instanceof Rule)
                P.add((Rule) rule);
        }
        return ImmutableCreator.create(P);
    }
    
    public ImmutableSet<Equation> getEsharp() {
        Set<Equation> Es = new HashSet<>();
        for (HasTermPair rule : this.g.getNodeObjects()) {
            if (rule instanceof Equation)
                Es.add((Equation) rule);
        }
        return ImmutableCreator.create(Es);
    }


    public String toDOT() {
        return this.g.toDOT(false);
    }
    
    /**
     * returns the internal graph. This graph must not be modified,
     * but may only be used for lookup-reasons.
     */
    public Graph<HasTermPair, ?> getGraph() {
        return this.g;
    }


}
