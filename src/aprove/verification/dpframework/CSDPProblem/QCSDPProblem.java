package aprove.verification.dpframework.CSDPProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Q-restricted Context Sensitive Dependency Pair Problem. Based on QDPProblem.
 * @author Fabian Emmes <fabian.emmes@rwth-aachen.de>
 * @version $Id$
 */
public class QCSDPProblem extends DefaultBasicObligation implements HTML_Able, DOT_Able {

    /** generate all cliques for collapsing DPs or just one */
    private static final boolean allCliques = false;

    /** true if minimal chains suffice */
    private final boolean minimal;

    /** cached value that is true, if NF^\mu(Q) \subseteq NF^\mu(R) */
    private Boolean innermost;

    /** dependency graph of the CS-DP-Problem */
    private final QCSDependencyGraph graph;

    /** the corresponding (non mu-restricted) QTRS problem */
    private final QTRSProblem rWithQ;

    /** the replacement map, including fresh symbols */
    private ReplacementMap rm;

    /** all defined symbols of the CSR */
    private final ImmutableSet<FunctionSymbol> definedSymbols;

    /** mapping from defined symbols to tuple symbols */
    private final ImmutableMap<FunctionSymbol, FunctionSymbol> defToTup;

    /**
     * all "normal" dependency pairs, plus pairs derived from collapsing DPs.
     * union of dp_o and dp_c.
     */
    private ImmutableSet<Rule> dp;

    /** all "normal" dependency pairs, if available */
    private final ImmutableSet<Rule> dp_o;

    /** all collapsing dependency pairs, if available */
    private final ImmutableSet<Rule> dp_c;

    /** all pairs derived from collapsing dependency pairs, if available */
    private final ImmutableSet<Rule> dp_u;

    /** set of hidden terms of R or null */
    private final ImmutableSet<TRSFunctionApplication> hiddenTerms;

    /** mapping of symbols to the set of positions they hide or null */
    private final ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> hidingSymbols;

    /** cached usable rules calculator */
    private QCSUsableRules urCalculator = null;

    private final Object signatureLock = new Object();

    private volatile ImmutableSet<FunctionSymbol> signature;

    private volatile ImmutableSet<FunctionSymbol> PRsignature;

    private volatile ImmutableSet<FunctionSymbol> headSymbols;

    /**
     * @param orig
     * @param newR
     */
    private QCSDPProblem(QCSDPProblem orig, ImmutableSet<Rule> newR) {
        super("QCSDP", "QSCDP-Problem");
        // FIXME insert assertion that newR is a subset of R, so we can keep
        // minimality
        this.minimal = orig.minimal;
        // FIXME filter these fields for unneeded stuff or generate new
        this.defToTup = orig.defToTup;
        this.dp = orig.dp;
        this.dp_o = orig.dp_o;
        this.dp_c = orig.dp_c;
        this.dp_u = orig.dp_u;
        // use new R
        this.rWithQ = QTRSProblem.create(newR, orig.rWithQ.getQ());
        this.definedSymbols = orig.definedSymbols;
        Set<FunctionSymbol> usedSymbols = this.getSignature();
        this.rm = ReplacementMap.create(orig.rm, usedSymbols);
        this.hidingSymbols = null;
        this.hiddenTerms = null;
        // update graph
        this.graph = QCSDependencyGraph.create(orig.graph, this);
    }

    private QCSDPProblem(CSRProblem csr, QTRSProblem rWithQ, boolean minimal) {
        super("QCSDP", "QSCDP-Problem");
        this.rWithQ = rWithQ;
        this.minimal = minimal;
        ReplacementMap interimRm = ReplacementMap.create(csr.getReplacementMap());
        this.definedSymbols = QCSDPProblem.computeDefinedSymbols(csr);
        this.hiddenTerms = QCSDPProblem.computeHiddenTerms(csr, interimRm, this.definedSymbols);
        this.hidingSymbols = QCSDPProblem.computeHidingSymbols(csr, interimRm, this.definedSymbols);
        FreshNameGenerator fng = new FreshNameGenerator(csr.getSignature(), FreshNameGenerator.DEPENDENCY_PAIRS);
        Map<FunctionSymbol, FunctionSymbol> defToTup = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
        Pair<ImmutableSet<Rule>, ImmutableSet<Rule>> p =
            QCSDPProblem.computeDPOandDPC(fng, defToTup, csr, interimRm, this.definedSymbols);
        this.dp_o = p.x;
        this.dp_c = p.y;
        this.defToTup = ImmutableCreator.create(defToTup);
        this.dp_u = QCSDPProblem.computeDPu(fng, this.dp_c, this.hidingSymbols, this.hiddenTerms, defToTup);
        this.dp = QCSDPProblem.computeDP(this.dp_o, this.dp_u);
        Set<FunctionSymbol> usedSymbols = this.getSignature();
        ReplacementMap interimRm2 = QCSDPProblem.completeReplacementMap(interimRm, defToTup, usedSymbols);
        this.rm = ReplacementMap.create(interimRm2, usedSymbols);
        this.graph = QCSDependencyGraph.create(this);
    }

    private static ImmutableSet<Rule> computeDPu(
        FreshNameGenerator fng,
        ImmutableSet<Rule> dpc,
        ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> hidingSymbols,
        ImmutableSet<TRSFunctionApplication> hiddenTerms,
        Map<FunctionSymbol, FunctionSymbol> defToTup
    ) {
        if (QCSDPProblem.allCliques) {
            return QCSDPProblem.computeDPuFull(fng, dpc, hidingSymbols, hiddenTerms, defToTup);
        } else {
            return QCSDPProblem.computeDPuMinimal(fng, dpc, hidingSymbols, hiddenTerms, defToTup);
        }
    }

    /**
     * QCSDPProblem from an SCC of an original problem.
     * @param orig the original QCSDPProblem
     * @param subgraph the SCC of the original problem
     */
    private QCSDPProblem(QCSDPProblem orig, QCSDependencyGraph subgraph) {
        super("QCSDP", "QSCDP-Problem");
        // TODO check which fields may be simplified
        this.minimal = orig.minimal;
        this.graph = subgraph;
        this.rWithQ = orig.rWithQ;
        Set<Rule> sccRules = new LinkedHashSet<Rule>();
        for (Node<Rule> node : subgraph.getNodes()) {
            sccRules.add(node.getObject());
        }
        this.definedSymbols = orig.definedSymbols;
        this.defToTup = orig.defToTup;
        /* only use rules occurring in the given SCC */
        if (orig.dp_o != null) {
            Set<Rule> dp_f = new LinkedHashSet<Rule>();
            for (Rule r : orig.dp_o) {
                if (sccRules.contains(r)) {
                    dp_f.add(r);
                }
            }
            this.dp_o = ImmutableCreator.create(dp_f);
        } else {
            this.dp_o = null;
        }
        if (orig.dp_u != null) {
            Set<Rule> dp_u = new LinkedHashSet<Rule>();
            for (Rule r : orig.dp_u) {
                if (sccRules.contains(r)) {
                    dp_u.add(r);
                }
            }
            this.dp_u = ImmutableCreator.create(dp_u);
        } else {
            this.dp_u = null;
        }
        this.dp_c = null;
        this.dp = ImmutableCreator.create(sccRules);
        Set<FunctionSymbol> usedSymbols = this.getSignature();
        this.rm = ReplacementMap.create(orig.rm, usedSymbols);
        this.hiddenTerms = null;
        this.hidingSymbols = null;
    }

    /**
     * Create a new {@link QCSDPProblem} with a reduced set of Pairs.
     * @param keptPairs
     * @param problem
     */
    private QCSDPProblem(ImmutableSet<Rule> keptPairs, QCSDPProblem problem) {
        super("QCSDP", "QSCDP-Problem");
        this.rWithQ = problem.rWithQ;
        this.definedSymbols = problem.definedSymbols;
        this.defToTup = problem.defToTup;
        // we can keep minimality!
        this.minimal = problem.minimal;
        this.hiddenTerms = null;
        this.hidingSymbols = null;
        this.dp = keptPairs;
        Set<FunctionSymbol> usedSymbols = this.getSignature();
        this.rm = ReplacementMap.create(problem.rm, usedSymbols);
        // FIXME maybe put pairs in corresponding set for beautiful output
        this.dp_o = null;
        this.dp_c = null;
        this.dp_u = null;
        // update graph
        this.graph = QCSDependencyGraph.create(problem.graph, this);
    }

    /**
     * Constructor for Pair Transformation Processors. Replaces oldPair by
     * newPair and updates Edges of DPGraph accordingly.
     * @param oldProblem
     * @param oldPair
     * @param newPairs
     */
    private QCSDPProblem(QCSDPProblem oldProblem, Rule oldPair, ImmutableSet<Rule> newPairs, boolean reconnectRhs) {
        super("QCSDP", "QSCDP-Problem");
        this.rWithQ = oldProblem.rWithQ;
        this.definedSymbols = oldProblem.definedSymbols;
        this.defToTup = oldProblem.defToTup;
        this.minimal = oldProblem.minimal;
        this.rm = oldProblem.rm;
        // update graph
        this.dp = oldProblem.dp;
        this.graph = QCSDependencyGraph.create(oldProblem.graph, this, oldPair, newPairs, reconnectRhs);
        this.dp = ImmutableCreator.create(this.graph.getGraph().getNodeObjects());
        Set<FunctionSymbol> usedSymbols = this.getSignature();
        this.rm = ReplacementMap.create(oldProblem.rm, usedSymbols);
        this.hiddenTerms = null;
        this.hidingSymbols = null;
        // FIXME maybe put pairs in corresponding set for beautiful output
        this.dp_o = null;
        this.dp_c = null;
        this.dp_u = null;
    }

    /**
     * create problem with new Q
     * @param orig
     * @param newQ
     */
    public QCSDPProblem(QCSDPProblem orig, QTermSet newQ) {
        super("QCSDP", "QSCDP-Problem");
        // FIXME insert assertion that newR is a subset of R, so we can keep
        // minimality
        this.minimal = orig.minimal;
        // FIXME filter these fields for unneeded stuff or generate new
        this.defToTup = orig.defToTup;
        this.dp = orig.dp;
        this.dp_o = orig.dp_o;
        this.dp_c = orig.dp_c;
        this.dp_u = orig.dp_u;
        // use new R
        this.rWithQ = QTRSProblem.create(orig.getR(), newQ);
        this.definedSymbols = orig.definedSymbols;
        Set<FunctionSymbol> usedSymbols = this.getSignature();
        this.rm = ReplacementMap.create(orig.rm, usedSymbols);
        this.hidingSymbols = null;
        this.hiddenTerms = null;
        // update graph
        this.graph = QCSDependencyGraph.create(orig.graph, this);
    }

    /**
     * generates a QCSDPProblem from an SCC of an original problem.
     * @param orig the original QCSDPProblem
     * @param subgraph the SCC of the original problem
     * @return the sub problem
     */
    public static QCSDPProblem create(QCSDPProblem orig, QCSDependencyGraph subgraph) {
        return new QCSDPProblem(orig, subgraph);
    }

    /**
     * Generates a {@link QCSDPProblem} from a new (reduced) set of Pairs.
     * @param keptPairs
     * @param problem
     * @return
     */
    public static QCSDPProblem create(ImmutableSet<Rule> keptPairs, QCSDPProblem problem) {
        return new QCSDPProblem(keptPairs, problem);
    }

    @Override
    public String export(Export_Util o) {
        /* Export_Util made me do this. Its not my fault. Really. */
        StringBuilder s = new StringBuilder();
        s.append(o.export("Q-restricted context-sensitive dependency pair problem:"));
        s.append(o.cond_linebreak());
        s.append(this.rm.export(o));
        s.append(o.cond_linebreak());
        if (this.dp_o != null && this.dp_c != null && this.dp_u != null) {
            if (!this.dp_o.isEmpty()) {
                s.append("The ordinary context-sensitive dependency pairs " + o.math("DP" + o.sub("o")) + " are:");
                s.append(o.set(this.dp_o, Export_Util.RULES));
                s.append(o.cond_linebreak());
            }
            if (!this.dp_c.isEmpty()) {
                s.append(o.export("The collapsing dependency pairs are "));
                s.append(o.math("DP" + o.sub("c")) + ":");
                s.append(o.set(this.dp_c, Export_Util.RULES));
                s.append(o.cond_linebreak());
            }
            if (!this.dp_u.isEmpty()) {
                s.append(o.cond_linebreak());
                if (this.hiddenTerms != null) {
                    s.append("The hidden terms of " + o.math("R") + " are:");
                    s.append(o.cond_linebreak());
                    s.append(o.set(this.hiddenTerms, Export_Util.RULES));
                }
                if (this.hidingSymbols != null) {
                    ArrayList<Exportable> hidingPosns = new ArrayList<Exportable>();
                    for (Map.Entry<FunctionSymbol, ImmutableSet<Integer>> e : this.hidingSymbols.entrySet()) {
                        final ArrayList<Integer> shiftSet = new ArrayList<Integer>(e.getValue().size());
                        for (Integer i : e.getValue()) {
                            shiftSet.add(i + 1);
                        }
                        hidingPosns.add(
                            new Exportable() {

                                private FunctionSymbol sym = e.getKey();

                                private ArrayList<Integer> set = shiftSet;

                                @Override
                                public String export(Export_Util eu) {
                                    return
                                        this.sym.export(eu)
                                        + " on positions "
                                        + eu.set(this.set, Export_Util.SIMPLESET);
                                }

                            }
                        );
                    }
                    s.append(o.cond_linebreak());
                    s.append(o.export("Every hiding context is built from:"));
                    s.append(o.set(hidingPosns, Export_Util.RULES));
                    s.append(o.cond_linebreak());
                }
                s.append(o.export("Hence, the new unhiding pairs " + o.math("DP" + o.sub("u")) + " are :"));
                s.append(o.set(this.dp_u, Export_Util.RULES));
                s.append(o.cond_linebreak());
            }
        } else {
            s.append(o.export("The TRS P consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.dp, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getR(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.getQ().getTerms().isEmpty()) {
            s.append("Q is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The set Q consists of the following terms:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.getQ().getTerms(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        return s.toString();
    }

    public boolean isGraphReducable() {
        if (this.isSeperable()) {
            return true;
        }
        Set<QCSDependencyGraph> subgraphs = this.graph.getSccSubGraphs();
        int remainingNodes = 0;
        for (QCSDependencyGraph graph : subgraphs) {
            remainingNodes += graph.getNodes().size();
        }
        // true if we can remove nodes
        return this.dp.size() > remainingNodes;
    }

    public Set<FunctionSymbol> getDefinedSymbols() {
        return this.definedSymbols;
    }

    public Map<FunctionSymbol, FunctionSymbol> getDefToTup() {
        return this.defToTup;
    }

    public final ImmutableSet<Rule> getDp() {
        return this.dp;
    }

    public ImmutableSet<Rule> getDPo() {
        return this.dp_o;
    }

    public ImmutableSet<Rule> getDPc() {
        return this.dp_c;
    }

    public ImmutableSet<Rule> getDPu() {
        return this.dp_u;
    }

    public final QCSDependencyGraph getGraph() {
        return this.graph;
    }

    public QTermSet getQ() {
        return this.rWithQ.getQ();
    }

    public ImmutableSet<Rule> getR() {
        return this.rWithQ.getR();
    }

    public final ReplacementMap getReplacementMap() {
        return this.rm;
    }

    public ReplacementMap getRm() {
        return this.rm;
    }

    /**
     * @return true if minimal chains suffice.
     */
    public final boolean isMinimal() {
        return this.minimal;
    }

    /**
     * @return true, if the problem is seperable to several subproblems, using
     * the sccs of the DP graph.
     */
    public boolean isSeperable() {
        return this.graph.isSeperable();
    }

    /**
     * create problem with new Q
     * @param oldProblem
     * @param newQ
     * @return
     */
    public static QCSDPProblem create(QCSDPProblem oldProblem, QTermSet newQ) {
        return new QCSDPProblem(oldProblem, newQ);
    }

    /**
     * creates a new QCSDPproblem.
     * @param csr the CSR the new problem is based on.
     * @param minimal true if we only consider minimal chains
     * @return the new QCSDPProblem
     */
    public static QCSDPProblem create(CSRProblem csr, boolean minimal) {
        ImmutableSet<Rule> r = csr.getR();
        QTermSet q;
        if (csr.getInnermost()) {
            ArrayList<TRSFunctionApplication> lhss = new ArrayList<TRSFunctionApplication>();
            for (Rule lr : r) {
                lhss.add(lr.getLeft());
            }
            q = new QTermSet(lhss);
        } else {
            q = new QTermSet(new ArrayList<TRSFunctionApplication>());
        }
        QTRSProblem rWithQ = QTRSProblem.create(r, q);
        return new QCSDPProblem(csr, rWithQ, minimal);
    }

    /**
     * creates a new problem where the pair oldPair was transformed to the
     * (possibly empty) set of pairs newPairs.
     * @param oldProblem
     * @param oldPair
     * @param newPairs
     * @return
     */
    public static QCSDPProblem create(
        QCSDPProblem oldProblem,
        Rule oldPair,
        ImmutableSet<Rule> newPairs,
        boolean reconnectRhs
    ) {
        return new QCSDPProblem(oldProblem, oldPair, newPairs, reconnectRhs);
    }

    public static QCSDPProblem create(QCSDPProblem orig, ImmutableSet<Rule> newR) {
        return new QCSDPProblem(orig, newR);
    }

    /**
     * Creates a problem which is like <code>problem</code>, but R and P are
     * reduced to keptRules and keptPairs, respectively. TODO improve
     * implementation (should be correct, but seems kinda wasteful)
     * @param keptPairs
     * @param keptRules
     * @param problem
     * @return
     */
    public static QCSDPProblem create(
        ImmutableSet<Rule> keptPairs,
        ImmutableSet<Rule> keptRules,
        QCSDPProblem problem
    ) {
        QCSDPProblem interim = QCSDPProblem.create(problem, keptRules);
        QCSDPProblem result = QCSDPProblem.create(keptPairs, interim);
        return result;
    }

    /**
     * Completes the replacementMap with entries for tupled symbols and fresh
     * uncovering symbols.
     * @param oldRm incomplete replacement map
     * @param defToTup mapping of defined symbols to tuple symbols
     * @param usedSymbols all symbols, including tuple symbols and fresh symbols
     * introduced uncovering rules
     * @return a replacement map with entries for tuple symbols and fresh
     * symbols
     */
    private static ReplacementMap completeReplacementMap(
        ReplacementMap oldRm,
        Map<FunctionSymbol, FunctionSymbol> defToTup,
        Set<FunctionSymbol> usedSymbols
    ) {
        Map<FunctionSymbol, ImmutableSet<Integer>> map = new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>();
        map.putAll(oldRm.getMap());
        // tuple symbols have the same active positions as norm
        for (Map.Entry<FunctionSymbol, FunctionSymbol> e : defToTup.entrySet()) {
            map.put(e.getValue(), map.get(e.getKey()));
        }
        // all other symbols fresh symbols (from DP_u) have empty sets...
        ImmutableSet<Integer> empty = ImmutableCreator.create(new LinkedHashSet<Integer>());
        for (FunctionSymbol s : usedSymbols) {
            if (!map.containsKey(s)) {
                map.put(s, empty);
            }
        }
        return ReplacementMap.create(map);
    }

    /**
     * computes the set of defined symbols
     * @param csr csr for which to compute the defined symbols
     * @return the defined symbols of the csr
     */
    private static ImmutableSet<FunctionSymbol> computeDefinedSymbols(CSRProblem csr) {
        Set<FunctionSymbol> defSyms = new LinkedHashSet<FunctionSymbol>();
        for (Rule rule : csr.getR()) {
            TRSFunctionApplication lhs = rule.getLeft();
            defSyms.add(lhs.getRootSymbol());
        }
        return ImmutableCreator.create(defSyms);
    }

    /**
     * Computes the union of DP_F and DP_u.
     * @param dp_f set of normal dependency pairs
     * @param dp_u set of pairs derived from collapsing dependency pairs
     * @return union of dp_f and dp_u
     */
    private static ImmutableSet<Rule> computeDP(Set<Rule> dp_f, Set<Rule> dp_u) {
        Set<Rule> dp = new LinkedHashSet<Rule>();
        dp.addAll(dp_f);
        dp.addAll(dp_u);
        return ImmutableCreator.create(dp);
    }

    /**
     * computes DP_F and DP_c. (Definition 1, [AGL06])
     * @param fng
     * @param defToTup will be updated with tuple symbols
     * @param csr csr, for which to compute the pairs
     * @return a pair containing DP_F on first and DP_X on second position.
     */
    private static Pair<ImmutableSet<Rule>, ImmutableSet<Rule>> computeDPOandDPC(
        FreshNameGenerator fng,
        Map<FunctionSymbol, FunctionSymbol> defToTup,
        CSRProblem csr,
        ReplacementMap rm,
        Set<FunctionSymbol> definedSymbols
    ) {
        Set<Rule> dp_o = new LinkedHashSet<Rule>();
        Set<Rule> dp_c = new LinkedHashSet<Rule>();
        // compute DP_o and DP_c
        for (Rule r : csr.getR()) {
            TRSFunctionApplication lhs = r.getLeft();
            FunctionSymbol f = lhs.getRootSymbol();
            FunctionSymbol leftTupleSym = QCSDPProblem.getTupleSymbol(f, defToTup, fng);
            TRSFunctionApplication dpLhs = TRSTerm.createFunctionApplication(leftTupleSym, lhs.getArguments());
            Set<TRSVariable> lhsVars = rm.getReplacingVariables(lhs);
            Set<TRSTerm> lhsTerms = rm.getReplacingSubterms(lhs);
            TRSTerm rhs = r.getRight();
            for (TRSTerm t : rm.getReplacingSubterms(rhs)) {
                if (t.isVariable()) {
                    // DP_c
                    TRSVariable v = (TRSVariable) t;
                    if (!lhsVars.contains(v)) {
                        dp_c.add(Rule.create(dpLhs, v));
                    }
                } else {
                    // DP_F
                    TRSFunctionApplication s = (TRSFunctionApplication) t;
                    // check lhs />_mu s
                    if (lhsTerms.contains(s) && !lhs.equals(s)) {
                        continue;
                    }
                    if (definedSymbols.contains(s.getRootSymbol())) {
                        FunctionSymbol rightTupleSym = QCSDPProblem.getTupleSymbol(s.getRootSymbol(), defToTup, fng);
                        TRSFunctionApplication dpRhs =
                            TRSTerm.createFunctionApplication(rightTupleSym, s.getArguments());
                        dp_o.add(Rule.create(dpLhs, dpRhs));
                    }
                }
            }
        }
        return
            new Pair<ImmutableSet<Rule>, ImmutableSet<Rule>>(
                ImmutableCreator.create(dp_o),
                ImmutableCreator.create(dp_c)
            );
    }

    private static FunctionSymbol getTupleSymbol(
        FunctionSymbol f,
        Map<FunctionSymbol, FunctionSymbol> defToTup,
        FreshNameGenerator fng
    ) {
        if (defToTup.containsKey(f)) {
            return defToTup.get(f);
        }
        int arity = f.getArity();
        String newName = fng.getFreshName(f.getName(), true);
        FunctionSymbol fSharp = FunctionSymbol.create(newName, arity);
        defToTup.put(f, fSharp);
        return fSharp;
    }

    /**
     * computes DP_u. ([GGLT07], Definition 11).
     * @param fng FreshNameGenerator used to generate tuple symbols
     * @param dp_c set of collapsing dependency pairs
     * @param hidingSymbols hiding symbols of the csr
     * @param hiddenTerms hidden terms of the csr
     * @param defToTup mapping from defined symbols to tuple symbols
     * @return the set of rules derived from the collapsing dependency pairs.
     */
    private static ImmutableSet<Rule> computeDPuFull(
        FreshNameGenerator fng,
        Set<Rule> dp_c,
        Map<FunctionSymbol, ImmutableSet<Integer>> hidingSymbols,
        Set<TRSFunctionApplication> hiddenTerms,
        Map<FunctionSymbol, FunctionSymbol> defToTup
    ) {
        Set<Rule> dp_u = new LinkedHashSet<Rule>();
        for (Rule rule : dp_c) {
            FunctionSymbol f = rule.getRootSymbol();
            String newName = fng.getFreshName(f.getName(), false);
            FunctionSymbol bigF = FunctionSymbol.create(newName, f.getArity());
            TRSFunctionApplication u = rule.getLeft();
            TRSVariable x = (TRSVariable) rule.getRight();
            // add u -> F(x)
            {
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(x);
                TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(bigF, ImmutableCreator.create(args));
                dp_u.add(Rule.create(u, rhs));
            }
            // add F(g(x_1,...,x_i,...,x_n)) -> F(x_i) for every g hiding i
            {
                for (Map.Entry<FunctionSymbol, ImmutableSet<Integer>> e : hidingSymbols.entrySet()) {
                    FunctionSymbol g = e.getKey();
                    ImmutableSet<Integer> g_map = e.getValue();
                    ArrayList<TRSTerm> gargs = new ArrayList<TRSTerm>();
                    int l = g.getArity();
                    for (int i = 0; i < l; ++i) {
                        gargs.add(TRSTerm.createVariable("x_" + i));
                    }
                    ArrayList<TRSTerm> fargs = new ArrayList<TRSTerm>();
                    fargs.add(TRSTerm.createFunctionApplication(g, ImmutableCreator.create(gargs)));
                    TRSFunctionApplication lhs =
                        TRSTerm.createFunctionApplication(bigF, ImmutableCreator.create(fargs));
                    for (Integer i : g_map) {
                        ArrayList<TRSTerm> rargs = new ArrayList<TRSTerm>();
                        rargs.add(TRSTerm.createVariable("x_" + i));
                        TRSFunctionApplication rhs =
                            TRSTerm.createFunctionApplication(bigF, ImmutableCreator.create(rargs));
                        dp_u.add(Rule.create(lhs, rhs));
                    }
                }
            }
            // F(t) -> t^# for every hidden term t
            for (TRSFunctionApplication t : hiddenTerms) {
                ArrayList<TRSFunctionApplication> fargs =
                    new ArrayList<TRSFunctionApplication>();
                fargs.add(t);
                TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(bigF, ImmutableCreator.create(fargs));
                TRSFunctionApplication tsharp =
                    TRSTerm.createFunctionApplication(
                        QCSDPProblem.getTupleSymbol(t.getRootSymbol(), defToTup, fng),
                        t.getArguments()
                    );
                dp_u.add(Rule.create(lhs, tsharp));
            }
        }
        return ImmutableCreator.create(dp_u);
    }

    /**
     * computes DP_u. ([GGLT07], Definition 11).
     * @param fng FreshNameGenerator used to generate tuple symbols
     * @param dp_c set of collapsing dependency pairs
     * @param hidingSymbols hiding symbols of the csr
     * @param hiddenTerms hidden terms of the csr
     * @param defToTup mapping from defined symbols to tuple symbols
     * @return the set of rules derived from the collapsing dependency pairs.
     */
    private static ImmutableSet<Rule> computeDPuMinimal(
        FreshNameGenerator fng,
        Set<Rule> dp_c,
        Map<FunctionSymbol, ImmutableSet<Integer>> hidingSymbols,
        Set<TRSFunctionApplication> hiddenTerms,
        Map<FunctionSymbol, FunctionSymbol> defToTup
    ) {
        Set<Rule> dp_u = new LinkedHashSet<Rule>();
        // if we have no collapsing pairs, we don't need any new rules
        if (dp_c.isEmpty()) {
            return ImmutableCreator.create(dp_u);
        }
        FunctionSymbol f = FunctionSymbol.create(fng.getFreshName("U", false), 1);
        for (Rule rule : dp_c) {
            TRSFunctionApplication u = rule.getLeft();
            TRSVariable x = (TRSVariable) rule.getRight();
            // add u -> F(x)
            {
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(x);
                TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(args));
                dp_u.add(Rule.create(u, rhs));
            }
        }
        // add F(g(x_1,...,x_i,...,x_n)) -> F(x_i) for every g hiding i
        {
            for (Map.Entry<FunctionSymbol, ImmutableSet<Integer>> e : hidingSymbols.entrySet()) {
                FunctionSymbol g = e.getKey();
                ImmutableSet<Integer> g_map = e.getValue();
                ArrayList<TRSTerm> gargs = new ArrayList<TRSTerm>();
                int l = g.getArity();
                for (int i = 0; i < l; ++i) {
                    gargs.add(TRSTerm.createVariable("x_" + i));
                }
                ArrayList<TRSTerm> fargs = new ArrayList<TRSTerm>();
                fargs.add(TRSTerm.createFunctionApplication(g, ImmutableCreator.create(gargs)));
                TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(fargs));
                for (Integer i : g_map) {
                    ArrayList<TRSTerm> rargs = new ArrayList<TRSTerm>();
                    rargs.add(TRSTerm.createVariable("x_" + i));
                    TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(rargs));
                    dp_u.add(Rule.create(lhs, rhs));
                }
            }
        }
        // F(t) -> t^# for every hidden term t
        for (TRSFunctionApplication t : hiddenTerms) {
            ArrayList<TRSFunctionApplication> fargs = new ArrayList<TRSFunctionApplication>();
            fargs.add(t);
            TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(fargs));
            TRSFunctionApplication tsharp =
                TRSTerm.createFunctionApplication(
                    QCSDPProblem.getTupleSymbol(t.getRootSymbol(), defToTup, fng),
                    t.getArguments()
                );
            dp_u.add(Rule.create(lhs, tsharp));
        }
        return ImmutableCreator.create(dp_u);
    }

    /**
     * computes hidden terms.
     * @param csr csr, for which to compute the hidden terms
     * @param rm replacement map of the csr
     * @param definedSymbols defined symbols of the csr
     * @return the set of hidden terms of the csr
     */
    private static ImmutableSet<TRSFunctionApplication> computeHiddenTerms(
        CSRProblem csr,
        ReplacementMap rm,
        Set<FunctionSymbol> definedSymbols
    ) {
        Set<TRSFunctionApplication> hiddenTerms = new LinkedHashSet<TRSFunctionApplication>();
        for (Rule lr : csr.getR()) {
            TRSTerm rhs = lr.getRight();
            for (TRSTerm t : rm.getNonReplacingSubterms(rhs)) {
                if (!t.isVariable()) {
                    TRSFunctionApplication ht = (TRSFunctionApplication) t;
                    if (definedSymbols.contains(ht.getRootSymbol())) {
                        hiddenTerms.add((TRSFunctionApplication) ht.getStandardRenumbered());
                    }
                }
            }
        }
        return ImmutableCreator.create(hiddenTerms);
    }

    /**
     * computes hiding symbols.
     * @param csr the csr for which to compute the symbols
     * @param definedSymbols defined symbols of the csr
     * @return hiding symbols of the csr
     */
    private static ImmutableMap<FunctionSymbol, ImmutableSet<Integer>> computeHidingSymbols(
        CSRProblem csr,
        ReplacementMap rm,
        Set<FunctionSymbol> definedSymbols
    ) {
        Map<FunctionSymbol, ImmutableSet<Integer>> hidingSymbols =
            new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>();
        for (Rule lr : csr.getR()) {
            TRSTerm rhs = lr.getRight();
            QCSDPProblem.findHidingSymbols(rhs, rm, definedSymbols, hidingSymbols);
        }
        return ImmutableCreator.create(hidingSymbols);
    }

    /**
     * Recursive function to compute the hiding symbols.
     * @param t Term to traverse, either is a rhs, or occured on a mu-replacing
     * position of a rhs.
     * @param definedSymbols
     * @param hidingSymbols will be completed with hiding symbols in t.
     */
    private static void findHidingSymbols(
        TRSTerm t,
        ReplacementMap rm,
        Set<FunctionSymbol> definedSymbols,
        Map<FunctionSymbol, ImmutableSet<Integer>> hidingSymbols
    ) {
        if (t.isVariable()) {
            return;
        }
        TRSFunctionApplication s = (TRSFunctionApplication) t;
        FunctionSymbol sym = s.getRootSymbol();
        int arity = sym.getArity();
        ImmutableSet<Integer> m = rm.getMap().get(sym);
        for (Integer i = 0; i < arity; ++i) {
            if (m.contains(i)) {
                QCSDPProblem.findHidingSymbols(s.getArgument(i), rm, definedSymbols,
                    hidingSymbols);
            } else {
                QCSDPProblem.findHidingSymbolsNonMu(s.getArgument(i), rm, definedSymbols,
                    hidingSymbols);
            }
        }
    }

    /**
     * Recursive function, which finds hiding symbols in t. Requires csr and
     * definedSymbols.
     * @param t term, which occurred on a non mu-replacing position of a rhs.
     * @param csr csr, for which to compute the hiding symbols
     * @param definedSymbols set of defined symbols of the csr
     * @param hidingSymbols will be completed with hiding symbols in t.
     * @return true if there was either a defined symbol or a variable in an
     * active position.
     */
    private static boolean findHidingSymbolsNonMu(
        TRSTerm t,
        ReplacementMap rm,
        Set<FunctionSymbol> definedSymbols,
        Map<FunctionSymbol, ImmutableSet<Integer>> hidingSymbols
    ) {
        if (t.isVariable()) {
            return true;
        }
        // true if subterm contains def. sym. or var. in active position.
        boolean rv = false;
        TRSFunctionApplication s = (TRSFunctionApplication) t;
        FunctionSymbol sym = s.getRootSymbol();
        int arity = sym.getArity();
        ImmutableSet<Integer> m = rm.getMap().get(sym);
        // positions that s hides
        Set<Integer> hides = new LinkedHashSet<Integer>();
        if (hidingSymbols.containsKey(sym)) {
            hides.addAll(hidingSymbols.get(sym));
        }
        for (Integer i = 0; i < arity; ++i) {
            if (m.contains(i)) {
                boolean maybeInf =
                    QCSDPProblem.findHidingSymbolsNonMu(s.getArgument(i), rm, definedSymbols, hidingSymbols);
                if (maybeInf) {
                    hides.add(i);
                }
                rv = rv || maybeInf;
            } else {
                QCSDPProblem.findHidingSymbolsNonMu(s.getArgument(i), rm, definedSymbols, hidingSymbols);
            }
        }
        if (rv) {
            hidingSymbols.put(sym, ImmutableCreator.create(hides));
        }
        // return true if this is a defined symbol or subterm contains def. sym.
        // or var. in active position
        return definedSymbols.contains(sym) || rv;
    }

    public final QTRSProblem getRWithQ() {
        return this.rWithQ;
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public ImmutableSet<Rule> getRInPrefixForm(String prefix) {
        Set<Rule> rules = new LinkedHashSet<Rule>();
        for (Rule l_to_r : this.rWithQ.getR()) {
            rules.add(l_to_r.getWithRenumberedVariables(prefix));
        }
        return ImmutableCreator.create(rules);
    }

    private synchronized void computeQCSUsableRules() {
        if (this.urCalculator != null) {
            return;
        }

        this.urCalculator = QCSUsableRules.create(this);
    }

    public QCSUsableRules getQCSUsableRules() {
        if (this.urCalculator == null) {
            this.computeQCSUsableRules();
        }
        return this.urCalculator;
    }

    public ImmutableSet<Rule> getUsableRules() {
        QCSUsableRules ur = this.getQCSUsableRules();
        return ur.estimatedCSUsableRules(this.getDp());
    }

    /**
     * returns the signature of P cup R cup Q
     */
    public ImmutableSet<FunctionSymbol> getSignature() {
        if (this.signature == null) {
            this.computeSignatures();
        }
        return this.signature;
    }

    /**
     * returns the signature of P cup R
     */
    public ImmutableSet<FunctionSymbol> getPRSignature() {
        if (this.signature == null) {
            this.computeSignatures();
        }
        return this.PRsignature;
    }

    public ImmutableSet<FunctionSymbol> getHeadSymbols() {
        if (this.signature == null) {
            this.computeSignatures();
        }
        return this.headSymbols;
    }

    private void computeSignatures() {
        synchronized (this.signatureLock) {
            if (this.signature == null) {
                if (Globals.useAssertions) {
                    assert (this.rWithQ != null);
                    assert (this.dp != null);
                }
                Set<FunctionSymbol> forbidden = new LinkedHashSet<FunctionSymbol>(this.rWithQ.getRSignature());
                Set<FunctionSymbol> headSyms = new LinkedHashSet<FunctionSymbol>();
                // headSyms and forbidden are disjoint!
                // in the end, headSyms should contain the head syms of P,R
                // and forbidden is the remaining signature of P \cup R
                for (Rule dp : this.dp) {
                    TRSFunctionApplication s = dp.getLeft();
                    // add non-root signature of s to forbidden
                    for (TRSTerm arg : s.getArguments()) {
                        for (FunctionSymbol f : arg.getFunctionSymbols()) {
                            if (forbidden.add(f)) {
                                headSyms.remove(f);
                            }
                        }
                    }
                    // add non-root signature of t to forbidden
                    TRSTerm t = dp.getRight();
                    if (!t.isVariable()) {
                        TRSFunctionApplication tt = (TRSFunctionApplication) t;
                        for (TRSTerm arg : tt.getArguments()) {
                            for (FunctionSymbol f : arg.getFunctionSymbols()) {
                                if (forbidden.add(f)) {
                                    headSyms.remove(f);
                                }
                            }
                        }
                        // add root-symbol of t
                        FunctionSymbol f = tt.getRootSymbol();
                        if (!forbidden.contains(f)) {
                            headSyms.add(f);
                        }
                    }
                    // add root-symbol of s
                    FunctionSymbol f = s.getRootSymbol();
                    if (!forbidden.contains(f)) {
                        headSyms.add(f);
                    }
                }
                forbidden.addAll(headSyms); // now forbidden = signature (P u R)
                Set<FunctionSymbol> fullSignature =
                    new LinkedHashSet<FunctionSymbol>(forbidden);
                fullSignature.addAll(this.getQ().getSignature());
                // and fullSignature = signature (P u R u Q)
                this.PRsignature = ImmutableCreator.create(forbidden);
                this.headSymbols = ImmutableCreator.create(headSyms);
                this.signature = ImmutableCreator.create(fullSignature);
            }
        }
    }

    private synchronized void computeInnermost() {
        if (this.innermost != null) {
            return;
        }
        boolean not_innermost = false;
        QTermSet q = this.rWithQ.getQ();
        for (Rule lr : this.rWithQ.getR()) {
            not_innermost =
                not_innermost || this.rm.inQMuNormalForm(q, lr.getLeft());
        }
        this.innermost = Boolean.valueOf(!not_innermost);
    }

    public boolean isInnermost() {
        if (this.innermost == null) {
            this.computeInnermost();
        }
        return this.innermost.booleanValue();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        throw new UnsupportedOperationException();
    }

    @Override
    public String toDOT() {
        return this.getGraph().getGraph().toDOT();
    }

    @Override
    public String getStrategyName() {
        return null;
    }

}
