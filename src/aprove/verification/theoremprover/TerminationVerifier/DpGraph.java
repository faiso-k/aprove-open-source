package aprove.verification.theoremprover.TerminationVerifier;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Rewriting.FunctionSymbolGraph;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Unification.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Diese Klasse stellt den Dependencypair Graphen dar.
 * @author Carsten Pelikan, Peter Schneider-Kamp, Stephan Falke, Achim Luecking
 * @version $Id$
 */
public class DpGraph extends Graph<Rule,Object> implements HTML_Able, LaTeX_Able, PLAIN_Able, java.io.Serializable {

    private GeneralUnification unif;
    private boolean equational;
    private Set<SyntacticFunctionSymbol> ACs = null;
    private Set<SyntacticFunctionSymbol> Cs = null;

    private Set<Rule> rules;
    private Set<Rule> dps;
    private boolean innermost;
    private Program program;

    private DpGraph() {

    }

    /**
     * True iff safe_nri is allowed.
     * first: narrow, second: rewrite, third: instantiate
     * (see DpNode for constants)
     */
//    public boolean safe[] = new boolean[]{true,true,true};

    /**
     * Erzeugt einen neuen Dependencypair Graphen.
     * @param dps Die Dependency Pairs, aus denen der Graph erzeugt wird.
     * @param rules Die Regeln, die zur Auswertung benutzt werden k~nnen.
     * @param innermost If this is set to true, innermost connectability will be considered.
     */
    public DpGraph(Set<Rule> dps, Set<Rule> rules, boolean innermost, Program prog) {

    super();
    this.dps = dps;
    this.rules = rules;
    this.innermost = innermost;
    this.program = prog;

    for (Node<Rule> node: this.determineNodes(dps)) {
        this.addNode(node);
    }

    if (prog != null) {
    this.unif = prog.getUnificator();
    this.ACs = prog.getACSymbols();
    this.Cs = prog.getCSymbols();
    this.equational = prog.isEquational();
    }

        for (Node<Rule> start : this.getNodes()) {
            for (Node<Rule> end : this.getNodes()) {
                this.connect(start, end, rules, innermost);
            }
        }

    }

    public DpGraph(Set<Node<Rule>> nodes, Set<Edge<Object, Rule>> edges){
        super(nodes, edges);
    }

    public DpGraph createRestrictedTo(Set<Rule> dps, Program prog, boolean innermost) {

        return new DpGraph(dps, prog.getRules(), innermost, prog);

    }

    public DpGraph shallowCopy() {

    DpGraph newG = new DpGraph(this.getNodes(), this);
    return newG;

    }

    public DpGraph(Set<Rule> dps, Set<Rule> rules, Program prog) {

    super();
    this.dps = dps;
    this.rules = rules;
    this.program = prog;
    this.innermost = false;
    for (Node<Rule> node : this.determineNodes(dps)) {
        this.addNode(node);
    }

    this.unif = prog.getUnificator();
    this.ACs = prog.getACSymbols();
    this.Cs = prog.getCSymbols();
    this.equational = prog.isEquational();

    for (Node<Rule> start : this.getNodes()) {
        for (Node<Rule> end : this.getNodes()) {
                this.connectSizeChange(start, end, rules);
            }
        }

    }

    /**
     * Creates a sub graph.
     */
    public DpGraph(Set<Node<Rule>> nodes, DpGraph supergraph) {
        super(nodes, supergraph);
        this.dps = supergraph.getDps();
        this.rules = supergraph.getRules();
        this.innermost = supergraph.getInnermost();
        this.program = supergraph.getProgram();
        this.equational = supergraph.equational;
        this.unif = supergraph.unif;
        this.ACs = supergraph.ACs;
        this.Cs = supergraph.Cs;
    }

    /**
     * Creates a sub graph.
     */
    public DpGraph(Set<Node<Rule>> nodes, DpGraph supergraph, Program prog) {
        super(nodes, supergraph);
    this.unif = prog.getUnificator();
    this.ACs = prog.getACSymbols();
    this.Cs = prog.getCSymbols();
    this.equational = prog.isEquational();
    this.dps = supergraph.getDps();
    this.rules = supergraph.getRules();
    this.innermost = supergraph.getInnermost();
    //prometheus says: This looks like a bug
    //this.program = program;
    //And THIS is the intended effect.
    this.program = prog;
    }

    /**
     * Create a sub graph of this graph.
     */
    @Override
    public DpGraph getSubGraph(Set<Node<Rule>> nodes) {
        return new DpGraph(nodes, this);
    }

    public Set<DpGraph> getSccs() {
        Set<Cycle<Rule>> cycles;
        cycles = this.getSCCs();
        Set<DpGraph> sccs = new LinkedHashSet<DpGraph>();
        for (Cycle<Rule> scc : cycles) {
            sccs.add(new DpGraph(scc,this));
        }
        return sccs;
    }

    /**
     * Create a dp graph from a given set of nodes.
     */
    public DpGraph(Set<Node<Rule>> nodes) {
        super(nodes);
    }

    /**
     * Berechnet aus einer gegebenen Menge von Regeln die Knoten des
     * Dependencypair Graphen.
     * @param rules Die Regeln, aus denen der Graph erzeugt wird.
     * @return Die Menge von Knoten des Dependencypair Graphen.
     */
    protected Set<Node<Rule>> determineNodes(Set<Rule> rules) {

        Set<Node<Rule>> nodes = new LinkedHashSet<Node<Rule>>();
        for (Rule rule : rules) {
            Node<Rule> node = new DpNode(rule);
            nodes.add(node);
        }

        return nodes;

    }

    /**
     * Berechnet aus einer gegebenen Menge von Regeln die Kanten des
     * Dependencypair Graphen.
     * @param nodes Die Knoten des Graphen. Aus den Regeln, die den Knoten
     * zugeordnet sind, k~nnen die Kanten berechnet werden.
     * @return Die Menge von Kanten des Dependencypair Graphen.
     */
    public Set<Edge> determineEdges(Set<Node> nodes) {
        Set<Edge> edges = new LinkedHashSet<Edge>();
        for (Node<Rule> startNode : nodes) {
            Rule startNodeRule = startNode.getObject();
            for (Node<Rule> endNode : nodes) {
                Rule endNodeRule = endNode.getObject();
                AlgebraTerm t = startNodeRule.getRight();
                AlgebraTerm v = endNodeRule.getLeft();
                if (this.connectable(t, v)) {
                    Edge<Object,Rule> edge = new Edge<Object,Rule>(startNode, endNode);
                    edges.add(edge);
                }
            }
        }

        return edges;
    }

    /**
    * Berechnet aus einer gegebenen Menge von Regeln die Kanten des
    * innermost Dependencypair Graphen.
    * @param nodes Die Knoten des Graphen. Aus den Regeln, die den Knoten
    * zugeordnet sind, k~nnen die Kanten berechnet werden.
    * @param rules Die Regeln, die zur Auswertung benutzt werden koennen.
    * @return Die Menge von Kanten des innermost Dependencypair Graphen.
    */
    public Set<Edge> determineInnermostEdges(
        Set<Node> nodes,
        Set<Rule> rules) {
        Set<Edge> edges = new LinkedHashSet<Edge>();
        for (Node<Rule> startNode : nodes) {
            Rule startNodeRule = startNode.getObject();
            for (Node<Rule> endNode : nodes) {
                Rule endNodeRule = endNode.getObject();
                AlgebraTerm s = startNodeRule.getLeft();
                AlgebraTerm t = startNodeRule.getRight();
                AlgebraTerm v = endNodeRule.getLeft();
                if (this.innermostConnectable(s, t, v, rules)) {
                    Edge<Object,Rule> edge = new Edge<Object,Rule>(startNode, endNode);
                    edges.add(edge);
                }
            }
        }

        return edges;
    }

    /**
    * Berechnet aus einer gegebenen Menge von Regeln die Kanten des
    * Dependencypair Graphen fuer die Size-Change-Nutzung.
    * @param nodes Die Knoten des Graphen. Aus den Regeln, die den Knoten
    * zugeordnet sind, k~nnen die Kanten berechnet werden.
    * @param rules Die Regeln, die zur Auswertung benutzt werden koennen.
    * @return Die Menge von Kanten des innermost Dependencypair Graphen.
    */
    public Set<Edge> determineSizeChangeEdges(
        Set<Node> nodes,
        Set<Rule> rules) {
        Set<Edge> edges = new LinkedHashSet<Edge>();
        for (Node<Rule> startNode : nodes) {
            Rule startNodeRule = (Rule)startNode.getObject();
            for (Node<Rule> endNode : nodes) {
                Rule endNodeRule = endNode.getObject();
                AlgebraTerm t = startNodeRule.getRight();
                AlgebraTerm v = endNodeRule.getLeft();
                if (this.connectableSizeChange(t, v)) {
                    Edge<Object,Rule> edge = new Edge<Object,Rule>(startNode, endNode);
                    edges.add(edge);
                }
            }
        }
        return edges;
    }

    /**
     * Create an edge between two nodes if they are connectable.
     */
    public boolean connect(Node<Rule> from, Node<Rule> to, Collection<Rule> rules, boolean innermost) {

        AlgebraTerm s = ((Rule) from.getObject()).getLeft();
        AlgebraTerm t = ((Rule) from.getObject()).getRight();
        AlgebraTerm v = ((Rule) to.getObject()).getLeft();
        if ((innermost && this.innermostConnectable(s, t, v, rules))
            || (!innermost && this.connectable(t, v))) {
            this.addEdge(from, to);
            return true;
        }
        return false;

    }

    /**
     * Create an edge between two nodes if they are connectable.
     */
    public boolean connectSizeChange(
        Node<Rule> from,
        Node<Rule> to,
        Collection<Rule> rules) {
        AlgebraTerm t = ((Rule)from.getObject()).getRight();
        AlgebraTerm v = ((Rule)to.getObject()).getLeft();
        if (this.connectableSizeChange(t, v)) {
            this.addEdge(from, to);
            return true;
        }
        return false;
    }

    /**
     * Pr???t, ob zwei Terme connactable sind.
     * @param t Ein Term.
     * @param v Ein Term.
     * @return true, falls beide Terme connectable sind.
     */
    public boolean connectable(AlgebraTerm t, AlgebraTerm v) {
    if(!t.getSymbol().equals(v.getSymbol())) {
        // no need for ren/cap and the like in this case...
        return false;
    }
        AlgebraTerm term = t.deepcopy();
        Set<AlgebraVariable> variables = v.getVars();
        variables.addAll(t.getVars());
        FreshVarGenerator generator = new FreshVarGenerator(variables);
//        System.out.println("Before: "+term.toString());
    if(this.equational) {
        term = term.capE(generator);
    }
    else {
            term = term.cap(generator);
    }
//        System.out.println("After CAP: "+term.toString());
        term = term.ren(generator, false);
//        System.out.println("After REN: "+term.toString());
//        System.out.println("The other: "+v.toString());
    if(this.equational) {
        term = term.getUntupleed();
        v = v.getUntupleed();
//        System.out.println("After untupleing: "+term.toString());
//        System.out.println("The other after untupleing: "+v.toString());
    }
//        System.out.println("Unifiable: "+Boolean.valueOf(this.unif.areUnifiable(term, v)).toString());
        if (this.unif != null) {
            return this.unif.areUnifiable(term, v);
        }
        return false;
    }

    /**
    * Checks whether two term are innermost connactable.
    * @param s Term, which subterms do not get replaced in.
    * @param t A term.
    * @param v A term.
    * @param rules The rules that can be applied.
    * @return true, if t and v are innermost connectable.
    */
    public boolean innermostConnectable(
        AlgebraTerm s,
        AlgebraTerm t,
        AlgebraTerm v,
        Collection<Rule> rules) {
    DefFunctionSymbol tsym = ((TupleSymbol)t.getSymbol()).getOrigin();
    DefFunctionSymbol ssym = ((TupleSymbol)s.getSymbol()).getOrigin();
    if((tsym.getTermination() && ssym.getTermination()) || !t.getSymbol().equals(v.getSymbol())) {
        // no need for ren/cap and the like in this case...
        return false;
    }
        AlgebraTerm term = t.deepcopy();
        Set<AlgebraVariable> variables = v.getVars();
        variables.addAll(t.getVars());
        FreshVarGenerator generator = new FreshVarGenerator(variables);
        // System.out.println("Left: "+s.toString());
        // System.out.println("Before: "+term.toString());
        term = term.cap(s, generator);
        //      System.out.println("After CAPs: "+term.toString());
        term = term.ren(generator, true);
        //      System.out.println("After RENonce: "+term.toString());
        //      System.out.println("The other: "+v.toString());
        //      System.out.println("Unifiable: "+Boolean.valueOf(term.isUnifiable(v)).toString());
        try {
            AlgebraSubstitution sub = term.unifies(v);
            //          System.out.println("Substitution is:"+sub.toString());
            //          Term smu = s.ren(generator, true).apply(sub);
            //          Term vmu = v.apply(sub);
            //          System.out.println("smu = "+smu+", vmu = "+vmu);
            //          System.out.println("smu NF = "+smu.isNormal(rules)+", vmu NF = "+vmu.isNormal(rules));
            return s.ren(generator, true).apply(sub).isNormal(rules) && v.apply(sub).isNormal(rules);
        } catch (UnificationException e) {
            return false;
        }
    }

    /**
     * Pr???t, ob zwei Terme connactable fuer SCT sind
     * @param t Ein Term.
     * @param v Ein Term.
     * @return true, falls beide Terme connectable sind.
     */
    public boolean connectableSizeChange(AlgebraTerm t, AlgebraTerm v) {
        return (t.getSymbol().equals(v.getSymbol()));
    }

    /**
    * Return a set of all defined function symbols that are
    * usable for this DpGraph.
    */
    public Set<DefFunctionSymbol> getUsableSymbols(
        Program prog,
        boolean innermost) {
        Set<DefFunctionSymbol> result =
            new LinkedHashSet<DefFunctionSymbol>();
        Iterator i = this.getNodeObjects().iterator();
        while (i.hasNext()) {
            Rule dp = (Rule)i.next();
            if (innermost) {
                result.addAll(dp.getRight().getDefFunctionSymbols());
            } else {
                TupleSymbol tuple = (TupleSymbol)dp.getRootSymbol();
                result.add(tuple.getOrigin());
            }
        }
        FunctionSymbolGraph fsg = prog.getCallGraph(false);
        Cycle<DefFunctionSymbol> reach = new Cycle<DefFunctionSymbol>();
        reach.addAll(
            fsg.determineReachableNodes(fsg.getNodesFromObjects(result)));
        result.addAll(reach.getNodeObjects());
        return result;
    }

    /**
     * Gives every node in the graph a unique label.
     */
    public void relabel() {
    int label = 1;
    Iterator iter = this.getNodes().iterator();
    while (iter.hasNext()) {
        ((DpNode)iter.next()).setLabel(label++);
    }
    }

    /**
     * Resets the instantiated-flag.
     */
    public void reset_instantiated() {
    Iterator iter = this.getNodes().iterator();
    while (iter.hasNext()) {
        ((DpNode)iter.next()).is_instantiated = false;
    }
    }

    public Set<Rule> getDps() {
        return this.dps;
    }

    public Set<Rule> getRules() {
        return this.rules;
    }

    public boolean getInnermost() {
        return this.innermost;
    }

    public Program getProgram() {
        return this.program;
    }

    /**
     * Resets the narrowed-flag.
     */
    public void reset_narrowed() {
    Iterator iter = this.getNodes().iterator();
    while (iter.hasNext()) {
        ((DpNode)iter.next()).is_narrowed = false;
    }
    }



    public static class NumNodesComparator implements Comparator<DpGraph> {

        public NumNodesComparator() {
            super();
        }

        @Override
        public int compare(DpGraph dpg1, DpGraph dpg2) {
            int result = dpg2.getNodes().size() - dpg1.getNodes().size();
            if (result == 0) {
                Iterator<Node<Rule>> i1 = dpg1.getNodes().iterator();
                Iterator<Node<Rule>> i2 = dpg2.getNodes().iterator();
                while (i1.hasNext() && i2.hasNext()) {
                    Node<Rule> node1 = i1.next();
                    Node<Rule> node2 = i2.next();
                    int newresult = node1.compareTo(node2);
                    if (newresult != 0) {
                        return newresult;
                    }
                }
            }
            return result;
        }

    }

    /**
     * Returns number of Nodes in DpGraph.
     */
    public int getSize() {
    return this.getNodes().size();
    }

    @Override
    public String toHTML() {
        StringBuffer temp = new StringBuffer();
        Iterator i = this.getNodes().iterator();
        while (i.hasNext()) {
            Node node = (Node)i.next();
            Rule rule = (Rule)node.getObject();
            temp.append("<B>");
            temp.append(rule.toHTML() + "</B>");
            if (i.hasNext()) {
                temp.append("<BR>");
            }
        }
        return temp.toString();
    }


    @Override
    public String toLaTeX() {
        StringBuffer temp = new StringBuffer();
        temp.append("\\begin{longtable}{lrcl}\n");
        Iterator i = this.getNodes().iterator();
        while (i.hasNext()) {
            Node node = (Node)i.next();
            Rule rule = (Rule)node.getObject();
            temp.append(rule.toLaTeX());
            if (i.hasNext()) {
                temp.append("\\\\ \n");
            } else {
                temp.append("\n");
            }
    }
        temp.append("\\end{longtable}\n");
        return temp.toString();
    }

    public String toLaTeXDOT() {
        return super.toLaTeX();
    }

    @Override
    public String toPLAIN() {
        StringBuffer temp = new StringBuffer();
        Iterator i = this.getNodes().iterator();
        while (i.hasNext()) {
            Node node = (Node)i.next();
            Rule rule = (Rule)node.getObject();
            temp.append(rule.toPLAIN());
            if (i.hasNext()) {
                temp.append("\n");
            }
        }
        return temp.toString();
    }

    /**
     * Returns a set containing the DPs of all nodes of this graph.
     * @return A set of the DPs of all nodes of this graph.
     */
    public Set<Rule> getDependencyPairs() {
        Set<Rule> dps = new LinkedHashSet<Rule>();
        Iterator i = this.getNodes().iterator();
        while (i.hasNext()) {
            Node node = (Node)i.next();
            Rule dp = (Rule)node.getObject();
            dps.add(dp);
        }
        return dps;
    }


    /**
     * throw away everything cache depending on the underlying TRS
     */
    public void invalidateProgramCache() {
        // nothing to do here
    }


    public DpGraph deepcopy() {
        return new DpGraph();
    }



}
