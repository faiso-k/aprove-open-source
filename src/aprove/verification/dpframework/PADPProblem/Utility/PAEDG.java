package aprove.verification.dpframework.PADPProblem.Utility;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.Equational.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * EDG for PADP problems.
 * Only sound if non-collapsing non-Z S-rules do not change the root symbol!
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class PAEDG implements Immutable {

    protected static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Utility.PAEDG");

    private final Graph<PARule, Object> g;
    private Set<FunctionSymbol> defs;
    private Set<FunctionSymbol> sdefs;
    private Set<FunctionSymbol> edefs;
    private ImmutableMap<String, ImmutableList<String>> sortMap;
    private Set<PARule> P;
    private Set<Rule> S;
    private Set<Equation> E;
    private PATRSProblem patrs;
    private Map<FunctionSymbol, FunctionSymbol> def_tup;
    private Abortion aborter;
    private Set<FunctionSymbol> pafuns;
    private Set<FunctionSymbol> paconstfuns;
    private ApproximationUnification unif;
    private Set<Cycle<PARule>> sccs; // the set of sccs of this graph, null if the graph itself is an SCC

    /*
     * create EDG
     */
    private PAEDG(PADPProblem padp, Abortion aborter) throws AbortionException {
        this.P = padp.getP();
        this.patrs = padp.getPATRS();
        this.def_tup = padp.getDefTup();
        this.defs = this.patrs.getDefinedSymbols();
        this.sdefs = this.patrs.getDefinedSymbolsOfS();
        this.edefs = this.patrs.getRootSymbolsOfE();
        this.S = this.patrs.getS();
        this.E = this.patrs.getE();
        this.unif = new ApproximationUnification(this.edefs);
        this.sortMap = this.patrs.getSortMap();
        this.aborter = aborter;

        this.pafuns = new LinkedHashSet<FunctionSymbol>();
        this.pafuns.add(FunctionSymbol.create("0", 0));
        this.pafuns.add(FunctionSymbol.create("1", 0));
        this.pafuns.add(FunctionSymbol.create("-", 1));
        this.pafuns.add(FunctionSymbol.create("+", 2));

        this.paconstfuns = new LinkedHashSet<FunctionSymbol>();
        this.paconstfuns.add(FunctionSymbol.create("0", 0));
        this.paconstfuns.add(FunctionSymbol.create("1", 0));

        Set<Node<PARule>> nodes = new LinkedHashSet<Node<PARule>>();
        for (PARule dp : this.P) {
            nodes.add(new Node<PARule>(dp));
        }

        this.g = new Graph<PARule, Object>(nodes);

        // first only check tuple symbols
        int n = nodes.size();
        List<Node<PARule>> nodeList = new Vector<Node<PARule>>(nodes);
        for (int i = 0; i < n; i++) {
            Node<PARule> fromNode = nodeList.get(i);
            PARule fromDP = fromNode.getObject();
            for (int j = i + 1; j < n; j++) {
                Node<PARule> toNode = nodeList.get(j);
                PARule toDP = toNode.getObject();
                // forward direction
                if (this.calculateFastConnection(fromDP, toDP)) {
                    this.g.addEdge(fromNode, toNode);
                }
                // backward direction
                if (this.calculateFastConnection(toDP, fromDP)) {
                    this.g.addEdge(toNode, fromNode);
                }
            }
            // self-cycle
            if (this.calculateFastConnection(fromDP, fromDP)) {
                this.g.addEdge(fromNode, fromNode);
            }
        }

        // now do real check on precomputed sccs
        this.computeSccs();
        this.checkEdgesOnSccs(aborter);
    }

    public static PAEDG create(PADPProblem padp, Abortion aborter) throws AbortionException {
        return new PAEDG(padp, aborter);
    }

    /*
     * only checks outermost symbols
     */
    private boolean calculateFastConnection(PARule from, PARule to) {
        TRSFunctionApplication t = (TRSFunctionApplication) from.getRight();
        TRSFunctionApplication s = to.getLeft();
        return t.getRootSymbol().equals(s.getRootSymbol());
    }

    /*
     * does the EDG check
     */
    private void checkEdgesOnSccs(Abortion aborter) throws AbortionException {
        List<Edge<?, PARule>> edges = new ArrayList<Edge<?, PARule>>(this.g.getEdges());
        boolean changed = false;
        if (this.sccs == null) {
            for (Edge<?, PARule> e : edges) {
                aborter.checkAbortion();
                Node<PARule> from = e.getStartNode();
                Node<PARule> to = e.getEndNode();
                if (!this.calculateConnection(from, to)) {
                    this.g.removeEdge(from, to);
                    changed = true;
                }
            }
        } else {
            Map<Node<PARule>, Cycle<PARule>> nodeToScc = new HashMap<Node<PARule>, Cycle<PARule>>(this.g.getNodes().size());
            for (Cycle<PARule> cycle : this.sccs) {
                for (Node<PARule> node : cycle) {
                    nodeToScc.put(node, cycle);
                }
            }
            for (Edge<?, PARule> e : edges) {
                aborter.checkAbortion();
                Node<PARule> from = e.getStartNode();
                Node<PARule> to = e.getEndNode();
                Cycle<PARule> fromCycle = nodeToScc.get(from);
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

    private int newnr;

    /**
     * does (an approximation of) the usual cap-based check
     * @throws AbortionException
     */
    private boolean calculateConnection(final Node<PARule> fromNode, final Node<PARule> toNode)
            throws AbortionException {
        PARule from = fromNode.getObject();
        PARule to = toNode.getObject();
        if (this.isPurePA(from.getRight(), false)) {
            // from.getRight can only be rewritten using S-rules for Z
            if (!this.isPurePA(to.getLeft(), false)) {
                // won't introduce new non-PA symbols in a chain
                return false;
            }
            if (this.isPurePA(to.getLeft(), true)) {
                // can use PA-unifiability
                PARule renamedFrom = this.renameVars(from);
                return this.calculateConnectionPurePA(renamedFrom, to);
            }
        }
        this.newnr = 0;
        TRSFunctionApplication capped_t = (TRSFunctionApplication) this.getCapped(from.getRight(), this.defs, false, null);
        if (this.isPurePA(capped_t, false) && this.isPurePA(to.getLeft(), true)) {
            // can use PA-unifiability
            PARule renamedFrom = this.renameVars(PARule.create(from.getLeft(), capped_t, from.getConstraint()));
            return this.calculateConnectionPurePA(renamedFrom, to);
        }
        if (this.isNoncollapsingForUniv(this.S) && !this.checkSymbols(capped_t, to.getLeft())) {
            // function clash
            return false;
        } else {
            // first check PA part (if any)
            PARule renamedFrom = this.renameVars(PARule.create(from.getLeft(), capped_t, from.getConstraint()));
            if (!this.calculateConnectionPAPart(renamedFrom, to)) {
                return false;
            }
            // check approximating unifiability
            if (this.isTotallyFree(capped_t)) {
                return renamedFrom.getRight().unifies(to.getLeft());
            } else {
                return this.unif.areUnifiable(this.getCapped(capped_t, this.sdefs, true, null), to.getLeft());
            }
        }
    }

    private boolean isTotallyFree(TRSFunctionApplication t) {
        if (!this.isBaseOnlyS(this.S) || !this.isBaseOnlyE(this.E)) {
            return false;
        }
        // check whether one argument has sort int
        FunctionSymbol ft = t.getRootSymbol();
        int arr = ft.getArity();
        ImmutableList<String> sorts = this.getSort(t.getRootSymbol());
        for (int i = 0; i < arr; i++) {
            if (sorts.get(i).equals("int")) {
                return false;
            }
        }
        // check function symbols
        for (Map.Entry<String, ImmutableList<String>> fsorts : this.sortMap.entrySet()) {
            String fname = fsorts.getKey();
            sorts = fsorts.getValue();
            int n = sorts.size();
            if (sorts.get(n - 1).equals("univ")) {
                for (int i = 0; i < n - 1; i++) {
                    if (sorts.get(i).equals("int")) {
                        // possible to go from univ to int
                        return false;
                    }
                }
            }
        }
        return true;
    }

    private boolean isBaseOnlyS(Set<Rule> rules) {
        for (Rule r : rules) {
            FunctionSymbol ft = r.getLeft().getRootSymbol();
            ImmutableList<String> sorts = this.getSort(ft);
            if (sorts.get(ft.getArity()).equals("univ")) {
                return false;
            }
        }
        return true;
    }

    private boolean isBaseOnlyE(Set<Equation> eqns) {
        for (Equation e : eqns) {
            FunctionSymbol ft = ((TRSFunctionApplication) e.getLeft()).getRootSymbol();
            ImmutableList<String> sorts = this.getSort(ft);
            if (sorts.get(ft.getArity()).equals("univ")) {
                return false;
            }
        }
        return true;
    }

    private boolean isNoncollapsingForUniv(Set<Rule> rules) {
        for (Rule r : rules) {
            if (r.getRight().isVariable()) {
                FunctionSymbol ft = r.getLeft().getRootSymbol();
                ImmutableList<String> sorts = this.getSort(ft);
                if (sorts.get(ft.getArity()).equals("univ")) {
                    return false;
                }
            }
        }
        return true;
    }

    private TRSTerm getCapped(TRSTerm t, Set<FunctionSymbol> toCap, boolean renameAllVars, String sort) {
        if (t.isVariable()) {
            if (renameAllVars || sort.equals("univ")) {
                this.newnr = this.newnr + 1;
                return TRSTerm.createVariable("!" + ((TRSVariable) t).getName() + (Integer.valueOf(this.newnr)).toString());
            } else {
                return t;
            }
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol troot = ft.getRootSymbol();
            if (toCap.contains(troot)) {
                this.newnr = this.newnr + 1;
                return TRSTerm.createVariable("!" + (Integer.valueOf(this.newnr)).toString());
            } else {
                int arr = troot.getArity();
                ImmutableList<String> sorts = this.getSort(troot);
                ArrayList<TRSTerm> newargs = new ArrayList<TRSTerm>();
                for (int i = 0; i < arr; i++) {
                    newargs.add(this.getCapped(ft.getArgument(i), toCap, renameAllVars, sorts.get(i)));
                }
                return TRSTerm.createFunctionApplication(troot, ImmutableCreator.create(newargs));
            }
        }
    }

    private ImmutableList<String> getSort(FunctionSymbol f) {
        ImmutableList<String> res = this.sortMap.get(f.getName());
        if (res == null) {
            res = this.sortMap.get(this.getDef(f).getName());
        }
        return res;
    }

    private boolean checkSymbols(TRSTerm s, TRSTerm t) {
        if(s.isVariable() || t.isVariable()) {
            return true;
        }
        TRSFunctionApplication sf = (TRSFunctionApplication) s;
        TRSFunctionApplication tf = (TRSFunctionApplication) t;
        FunctionSymbol sSymb = sf.getRootSymbol();
        FunctionSymbol tSymb = tf.getRootSymbol();
        boolean sAlien = this.sdefs.contains(sSymb);
        boolean tAlien = this.sdefs.contains(tSymb);
        if(sAlien != tAlien) {
            // alien and non-alien don't mix
            return false;
        }
        boolean res = sSymb.equals(tSymb);
        if (this.pafuns.contains(sSymb)) {
            // since, e.g., 0 + 0 -> 0
            res = true;
        }
        if(res && !sAlien && !tAlien) {
            // check arguments
            int arr = sSymb.getArity();
            for (int i = 0; res && i < arr; i++) {
                res = this.checkSymbols(sf.getArgument(i), tf.getArgument(i));
            }
        }
        return res;
    }

    private boolean isPurePA(TRSTerm t, boolean onlyConstVar) {
        TRSFunctionApplication ft = (TRSFunctionApplication) t;
        FunctionSymbol f = ft.getRootSymbol();
        List<String> fsorts = this.sortMap.get(this.getDef(f).getName());
        int arr = f.getArity();
        for (int i = 0; i < arr; i++) {
            if (!fsorts.get(i).equals("int")) {
                return false;
            }
        }

        Set<FunctionSymbol> funs = new LinkedHashSet<FunctionSymbol>();
        for (TRSTerm arg : ft.getArguments()) {
            funs.addAll(arg.getFunctionSymbols());
        }
        if (onlyConstVar) {
            return this.paconstfuns.containsAll(funs);
        } else {
            return this.pafuns.containsAll(funs);
        }
    }

    private FunctionSymbol getDef(FunctionSymbol f) {
        for (FunctionSymbol g : this.def_tup.keySet()) {
            if (this.def_tup.get(g).equals(f)) {
                return g;
            }
        }
        return null;
    }

    private PARule renameVars(PARule rule) {
        Set<TRSVariable> allVars = new LinkedHashSet<TRSVariable>();
        allVars.addAll(rule.getLeft().getVariables());
        allVars.addAll(rule.getRight().getVariables());
        for (PAConstraint c : rule.getConstraint()) {
            allVars.addAll(c.getVariables());
        }

        Map<TRSVariable, TRSTerm> submap = new HashMap<TRSVariable, TRSTerm>();
        for (TRSVariable v : allVars) {
            submap.put(v, TRSTerm.createVariable("!" + v.getName()));
        }

        TRSSubstitution rename = TRSSubstitution.create(ImmutableCreator.create(submap));

        TRSFunctionApplication newl = rule.getLeft().applySubstitution(rename);
        TRSFunctionApplication newr = ((TRSFunctionApplication) rule.getRight()).applySubstitution(rename);
        Set<PAConstraint> newc = new LinkedHashSet<PAConstraint>();
        for (PAConstraint c : rule.getConstraint()) {
            newc.add(PAConstraint.create(c.getLeft().applySubstitution(rename), c.getRight().applySubstitution(rename), c.getType()));
        }

        return PARule.create(newl, newr, ImmutableCreator.create(newc));
    }

    private boolean calculateConnectionPurePA(final PARule from, final PARule to) throws AbortionException {
        TRSFunctionApplication t = (TRSFunctionApplication) from.getRight();
        TRSFunctionApplication s = to.getLeft();
        Set<PAConstraint> tmp = new LinkedHashSet<PAConstraint>();
        tmp.addAll(from.getConstraint());
        tmp.addAll(to.getConstraint());
        tmp.addAll(this.createEqualities(t.getArguments(), s.getArguments()));

        if (YicesChecker.callYices(PAConstraint.toSMTLIB(tmp), PAEDG.log, this.aborter) == YNM.NO) {
            return false;
        } else {
            return true;
        }
    }

    private boolean calculateConnectionPAPart(final PARule from, final PARule to) throws AbortionException {
        TRSFunctionApplication t = (TRSFunctionApplication) from.getRight();
        TRSFunctionApplication s = to.getLeft();
        Set<PAConstraint> tmp = new LinkedHashSet<PAConstraint>();
        tmp.addAll(from.getConstraint());
        tmp.addAll(to.getConstraint());
        ArrayList<TRSTerm> tss = new ArrayList<TRSTerm>();
        ArrayList<TRSTerm> sss = new ArrayList<TRSTerm>();
        int arr = t.getRootSymbol().getArity();
        for (int i = 0; i < arr; i++) {
            if (this.hasOnlyPA(t.getArgument(i), false) && this.hasOnlyPA(s.getArgument(i), true)) {
                tss.add(t.getArgument(i));
                sss.add(s.getArgument(i));
            }
        }
        tmp.addAll(this.createEqualities(ImmutableCreator.create(tss), ImmutableCreator.create(sss)));

        if (YicesChecker.callYices(PAConstraint.toSMTLIB(tmp), PAEDG.log, this.aborter) == YNM.NO) {
            return false;
        } else {
            return true;
        }
    }

    private boolean hasOnlyPA(TRSTerm t, boolean onlyConstVar) {
        Set<FunctionSymbol> funs = t.getFunctionSymbols();
        if (onlyConstVar) {
            return this.paconstfuns.containsAll(funs);
        } else {
            return this.pafuns.containsAll(funs);
        }
    }

    private Set<PAConstraint> createEqualities(
        ImmutableList<? extends TRSTerm> l1,
        ImmutableList<? extends TRSTerm> l2
    ) {
        int n = l1.size();
        Set<PAConstraint> res = new LinkedHashSet<PAConstraint>();
        for (int i = 0; i < n; i++) {
            res.add(PAConstraint.create(l1.get(i), l2.get(i), PAConstraint.EQ));
        }
        return res;
    }

    private void computeSccs() {
        Set<Cycle<PARule>> sccs = this.g.getSCCs();
        if (sccs.size() == 1 && sccs.iterator().next().size() == this.g.getNodes().size()) {
            this.sccs = null;
        } else {
            this.sccs = sccs;
        }
    }

    public boolean isSCC() {
        return this.sccs == null;
    }

    public ImmutableSet<PADPProblem> getSCCs() {
        Set<PADPProblem> subSccs = new LinkedHashSet<PADPProblem>();
        for (Set<Node<PARule>> scc : this.sccs) {
            subSccs.add(this.getSubProblem(scc));
        }
        return ImmutableCreator.create(subSccs);
    }

    private PADPProblem getSubProblem(Set<Node<PARule>> scc) {
        Set<PARule> newP = new LinkedHashSet<PARule>();
        for (Node<PARule> node : scc) {
            newP.add(node.getObject());
        }
        return PADPProblem.create(ImmutableCreator.create(newP), this.patrs, this.def_tup);
    }

    public ImmutableSet<PARule> getP() {
        return ImmutableCreator.create(this.g.getNodeObjects());
    }

    public String toDOT() {
        return this.g.toDOT(false);
    }

}
