package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class NarrowingGraphToNonTermDPs extends NarrowingGraphToDPs {

    private final BasicInstanceChecker bic;
    private final ConsEntity listNil;
    private final ConsEntity listCons;
    private VarEntity ccCheckEntity;
    private Set<TyClassEntity> ccUsedTyClasses;

    public NarrowingGraphToNonTermDPs(final Modules modules, final NarrowNode freeAppNode) {
        super(modules, freeAppNode);
        this.bic = new BasicInstanceChecker(modules.getCcg());
        this.listNil = this.modules.getPrelude().getListNil();
        this.listCons = this.modules.getPrelude().getListCons();
        this.ccCheckEntity = null;
    }

    public VarEntity getCcCheckEntity() {
        return this.ccCheckEntity;
    }

    @Override
    public void buildDPGraph(NarrowNode root, final NarrowNode node, final Graph<NarrowNode, Object> target) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            // System.out.println("CurrentA: "+node+" root "+root);
        }

        final boolean visited = (node.getMark() == target);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            // System.out.println("CurrentB: "+node);
        }

        node.setMark(target);
        if ((!visited) && (target.getNodeFromObject(node) == null)) {
            target.addNode(new Node<NarrowNode>(node));
        }
        if (node.isRoot()) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                // System.out.println("SCCGraph: "+node);
            }

            if (root != null) {
                final Node<NarrowNode> rnode = target.getNodeFromObject(root);
                final Node<NarrowNode> nnode = target.getNodeFromObject(node);

                target.addEdge(rnode, nnode);

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    // System.out.println(root+" --- "+node);
                }
            }
            root = node;
        }
        if (visited) {
            return;
        }

        // Don't go over ParSplit(Var)-nodes, i.e. Mode.UNIVAR
        /*
         * actually, we may consider ParSplit(Var) nodes here, since these are OK on the path to an SCC.
         * Only in the SCC, we must not have such nodes, this is checked in buildCallsWithConstraints().
         *
        if (node.getMode() == Mode.UNIVAR) {
            return;
        }
        */

        // include children of ParSplit(Cons)-nodes, since for these the constraints must be accumulated
        if (node.getMode() == Mode.CONS) {
            if (node.getChildren() != null) {
                final Node<NarrowNode> rnode = target.getNodeFromObject(root);
                for (final NarrowNode child : node.getChildren()) {
                    if (root != null) {
                        Node<NarrowNode> nnode = target.getNodeFromObject(child);
                        if (nnode == null) {
                            nnode = new Node<NarrowNode>(child);
                            target.addNode(nnode);
                        }
                        target.addEdge(rnode, nnode);
                    }
                    this.buildDPGraph(child, child, target);
                }
            }
            return;
        }

        if (node.getMode() == Mode.INSTANCE) {
            final InstanceAnnotation instanceAnnotation = (InstanceAnnotation) node.getAnnotation();
            this.buildDPGraph(root, instanceAnnotation.getBase(), target);
        }
        // Do not build further top-level SCCs for instance nodes, thus the "else"
        else if (node.getChildren() != null) {
            for (final NarrowNode child : node.getChildren()) {
                this.buildDPGraph(root, child, target);
            }
        }
    }

    /**
     * Determine the SCCs that are known to be reachable from the start term, i.e. no instantiation edges,
     * and at every ParSplit-node the set of class constraints is known to be satisfiable
     * @param sccs The set of top level SCCs
     * @param graph The graph of the SCCs
     * @param startTerm The start-term in the Narrowing Graph
     * @return The set of SCCs that are known to be reachable
     */
    private Set<Cycle<NarrowNode>> getKnownReachableSCCs(final Set<Cycle<NarrowNode>> sccs,
        final Graph<NarrowNode, Object> graph,
        final NarrowNode startTerm) {
        final Set<Cycle<NarrowNode>> remainingSCCs = new HashSet<Cycle<NarrowNode>>(sccs);
        final Set<Cycle<NarrowNode>> reachableSCCs = new HashSet<Cycle<NarrowNode>>();
        final Queue<NarrowNode> todo = new LinkedList<NarrowNode>();
        todo.add(startTerm);
        while ((!remainingSCCs.isEmpty()) && (!todo.isEmpty())) {
            final NarrowNode nnode = todo.remove();

            // don't go over Ins-nodes
            if (nnode.getMode() == Mode.INSTANCE) {
                continue;
            }

            // Here, we go over ParSplit(Var)-nodes, since we are in the prefix.
            // Thus, a function that needs to be evaluated only once exists.

            // but, at ParSplit- and Eval-nodes, check whether there exists a basic instance.
            // This ensures, that all "independent" class constraints of those of the SCCs below have a basic instance.
            // Note, that Eval-nodes need this check only on the path leading to the SCC,
            // since inside the SCC existance of them is guaranteed,
            // as their class constraints come from the root-node above
            // and they produce only a single child, where no interdependent class constraints can occur.
            if ((nnode.getMode() == Mode.CONS) || (nnode.getMode() == Mode.UNIVAR) || (nnode.getMode() == Mode.NON)) {
                if (!this.bic.hasBasicInstance(nnode.getConstraints())) {
                    // we have not found a basic instance for this node => the SCCs below are not known to be reachable
                    continue;
                }
            }

            final Node<NarrowNode> gnode = graph.getNodeFromObject(nnode);
            for (final Iterator<Cycle<NarrowNode>> scc_it = remainingSCCs.iterator(); scc_it.hasNext();) {
                final Cycle<NarrowNode> scc = scc_it.next();
                if (scc.contains(gnode)) {
                    reachableSCCs.add(scc);
                    scc_it.remove();
                }
            }
            todo.addAll(nnode.getChildren());
        }

        return reachableSCCs;
    }

    @Override
    public List<HaskellPR> buildDPs(final NarrowNode tree) {
        final List<HaskellPR> hprs = new Vector<HaskellPR>();
        final Graph<NarrowNode, Object> graph = new Graph<NarrowNode, Object>();
        this.buildDPGraph(null, tree, graph);
        int j = 0;

        Set<Cycle<NarrowNode>> sccs = graph.getSCCs();
        sccs = this.getKnownReachableSCCs(sccs, graph, tree);

        for (final Cycle<NarrowNode> scc : sccs) {
            final List<Pair<HaskellExp, HaskellExp>> dps = new Vector<Pair<HaskellExp, HaskellExp>>();
            final List<Pair<HaskellExp, HaskellExp>> rules = new Vector<Pair<HaskellExp, HaskellExp>>();
            final Set<NarrowNode> usableFunctions = new HashSet<NarrowNode>();
            this.ccUsedTyClasses = new HashSet<TyClassEntity>();
            this.buildDPsForSCC(scc.getNodeObjects(), dps, usableFunctions);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                int i = 0;
                for (final Pair<HaskellExp, HaskellExp> dp : dps) {
                    i++;

                    //System.out.println(j+"DP"+i+":  "+dp.x+" ==> "+dp.y);
                }
            }

            j++;

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(usableFunctions);
            }

            for (final NarrowNode node : usableFunctions) {
                this.buildRulesForNode(node, rules);
            }

            // check, whether we had a right-hand side which required class constraints
            if (this.ccCheckEntity != null) {
                // build up the complete set of used type classes (since there might be a ClassConstraintRule such as A [a] <= C a,
                // where the type class C was not used before
                boolean changed;
                do {
                    changed = false;
                    for (final ClassConstraintRule ccr : this.modules.getCcg().getRules()) {
                        if (this.ccUsedTyClasses.contains(ccr.getPattern().getTyClass().getEntity())) {
                            for (final ClassConstraint cc : ccr.getResults()) {
                                changed |= this.ccUsedTyClasses.add((TyClassEntity) cc.getTyClass().getEntity());
                            }
                        }
                    }
                } while (changed);

                for (final ClassConstraintRule ccr : this.modules.getCcg().getRules()) {
                    if (!this.ccUsedTyClasses.contains(ccr.getPattern().getTyClass().getEntity())) {
                        // only include the used type classes
                        continue;
                    }

                    HaskellExp ccLhs, ccRhs;
                    final VarEntity ccsEntity = new VarEntity("ccs", this.modules.getPrelude(), null, null, true);
                    ccLhs = new Apply(new Cons(ccr.getPattern().getTyClass()), ccr.getPattern().getType());
                    ccLhs =
                        new Apply(new Apply(new Cons(new HaskellNamedSym(this.listCons)), ccLhs), new Var(
                            new HaskellNamedSym(ccsEntity)));
                    ccLhs = new Apply(new Var(new HaskellNamedSym(this.ccCheckEntity)), ccLhs);

                    ccRhs = new Var(new HaskellNamedSym(ccsEntity));
                    for (final ClassConstraint cc : ccr.getResults()) {
                        ccRhs =
                            new Apply(new Apply(new Cons(new HaskellNamedSym(this.listCons)), new Apply(new Cons(
                                cc.getTyClass()), cc.getType())), ccRhs);
                    }
                    ccRhs = new Apply(new Var(new HaskellNamedSym(this.ccCheckEntity)), ccRhs);

                    rules.add(new Pair<HaskellExp, HaskellExp>(ccLhs, ccRhs));
                }
                HaskellExp ccEmptyLhs, ccEmptyRhs;
                ccEmptyLhs =
                    new Apply(new Var(new HaskellNamedSym(this.ccCheckEntity)), new Cons(new HaskellNamedSym(
                        this.listNil)));
                ccEmptyRhs = new Cons(new HaskellNamedSym(this.listNil));
                rules.add(new Pair<HaskellExp, HaskellExp>(ccEmptyLhs, ccEmptyRhs));
            }

            hprs.add(new HaskellPR(dps, rules));
        }
        return hprs;
    }

    @Override
    public void buildDPsForSCC(final Set<NarrowNode> scc,
        final Collection<Pair<HaskellExp, HaskellExp>> target,
        final Set<NarrowNode> usableFunctions) {
        for (final NarrowNode node : scc) {
            this.buildDPsForNode(node, target, scc, usableFunctions);
        }
    }

    @Override
    public void buildDPsForNode(final NarrowNode node,
        final Collection<Pair<HaskellExp, HaskellExp>> target,
        final Set<NarrowNode> scc,
        final Set<NarrowNode> usableFunctions) {
        if (!node.isRoot()) {
            // not a root node, i.e. no DPs start here...
            return;
        }

        final HaskellExp oleft = node.getExpression();
        final HaskellExp lhead = (HaskellExp) HaskellTools.applyFlatten(oleft).get(0);
        if (lhead instanceof Var) {
            if (((Var) lhead).getSymbol().getEntity() == this.errorEntity) {
                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println("no error dp");
                }

                return;
            }
        }
        final HaskellExp left = this.buildReplaceFor(NarrowingGraphAnalyser.DPsReplacer, node);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("$DPS$  "+node.num+"---"+left);
        }

        final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> srhss =
            new Vector<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>>();
        this.buildCalls(new HaskellSubstitution(), new HaskellSubstitution(), node, srhss, scc, usableFunctions, true);
        for (final Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp> srhs : srhss) {
            HaskellExp lhs = (HaskellExp) srhs.y.applyTo((BasicTerm) left);
            (new TypeAnnotationSubstitutor(srhs.x)).applyTo(lhs);
            final HaskellExp olhs = (HaskellExp) srhs.y.applyTo((BasicTerm) oleft);

            lhs = (HaskellExp) srhs.x.applyTo((BasicTerm) lhs);

            (new TypeAnnotationSubstitutor(srhs.x)).applyTo(olhs);
            final HaskellExp rhs = srhs.z;

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(olhs);
                System.out.println(lhs + " --> " + rhs);
                //System.out.println();
            }

            lhs = new Apply(lhs, new Cons(new HaskellNamedSym(this.listNil)));

            target.add(new Pair<HaskellExp, HaskellExp>(lhs, rhs));
        }
    }

    @Override
    public void buildCalls(final HaskellSubstitution tySubs,
        final HaskellSubstitution subs,
        final NarrowNode node,
        final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> target,
        final Collection<NarrowNode> scc,
        final Collection<NarrowNode> usableFunctions,
        final boolean head) {
        this.buildCallsWithConstraints(tySubs, subs, node, target, scc, usableFunctions, head, node.getConstraints());
        return;
    }

    /**
     * Worker function of {@link #buildCalls(HaskellSubstitution, HaskellSubstitution, NarrowNode, List, Collection, Collection, boolean)}.
     * Constructs the DP paths for a node in an SCC that was constructed from Top-Cycles only.
     * All class constraints of a node are added as a list to the term, thus a class constraint reduction function must be included in R.
     * @param tySubs Substitutions on type variables (TyCase)
     * @param subs Substitutions on term variables (Case)
     * @param node The current node
     * @param target Output parameter; will contain triples of a type substitution,
     *                                 a term substitution (both accumulated over the DP path),
     *                                 and a term that is the end of the DP path
     * @param scc The current SCC to create DPs for
     * @param usableFunctions Output parameter; will contain nodes from which the usable rules must be read
     * @param head Whether this is a head symbol, unused
     * @param ccs The current set of class constraints that must be fulfilled in order to be sure that this path is reachable by a
     *                                 ground instance of the start term
     */
    private void buildCallsWithConstraints(final HaskellSubstitution tySubs,
        final HaskellSubstitution subs,
        final NarrowNode node,
        final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> target,
        final Collection<NarrowNode> scc,
        final Collection<NarrowNode> usableFunctions,
        final boolean head,
        final Set<ClassConstraint> ccs) {
        switch (node.getMode()) {
        case CONS:
            if (node.getChildren() != null) {
                final Set<ClassConstraint> newCCs = new HashSet<ClassConstraint>();

                // accumulate CCs of the children that are on the SCC
                for (final NarrowNode child : node.getChildren()) {
                    if (scc.contains(child)) {
                        newCCs.addAll(child.getConstraints());
                    }
                }

                final Set<ClassConstraint> remCCs = new HashSet<ClassConstraint>(ccs);
                remCCs.removeAll(newCCs);
                if (!this.bic.hasBasicInstance(remCCs)) {
                    // we are not sure that the remaining class constraints (independent CCs) can be fulfilled => do not follow
                    return;
                }

                for (final NarrowNode child : node.getChildren()) {
                    this.buildCallsWithConstraints(tySubs, subs, child, target, scc, usableFunctions, false, newCCs);
                }
            }
            return;

        case NON:
        case VAREXP:
            // An Eval-node might throw away class constraints.
            // This is not done here, since this class constraint might have been introduced previously on this cycle
            for (final NarrowNode child : node.getChildren()) {
                final Set<ClassConstraint> newCCs = new HashSet<ClassConstraint>(ccs);
                newCCs.addAll(node.getConstraints());
                this.buildCallsWithConstraints(tySubs, subs, child, target, scc, usableFunctions, false, newCCs);
            }
            return;

        case UNIVAR:
            // don't follow ParSplit(Var)-nodes, since they cannot be guaranteed to be instantiable correctly,
            // such that the infinite evaluation could continue
            return;

        case CASE: {
            final Iterator<HaskellSubstitution> it = ((CaseAnnotation) node.getAnnotation()).getSubstitutions().iterator();
            for (final NarrowNode child : node.getChildren()) {
                this.buildCallsWithConstraints(tySubs, subs.combineWith(it.next()), child, target, scc,
                    usableFunctions, false, ccs);
            }
            return;
        }
        case TYCASE: {
            if (node.getChildren().isEmpty()) {
                // no children mean nothing to do...
                return;
            }

            // Type variables are identified by their HaskellSym, they do not have an entity
            final HaskellSubstitution firstTyCaseSubs = ((TyCaseAnnotation) node.getAnnotation()).getTySubstitutions().get(0);
            final HaskellSym tyVarSym = firstTyCaseSubs.keySet().iterator().next();
            final Set<ClassConstraint> baseCCs = new HashSet<ClassConstraint>(ccs);
            for (final Iterator<ClassConstraint> cc_it = baseCCs.iterator(); cc_it.hasNext();) {
                final ClassConstraint cc = cc_it.next();
                final Set<HaskellSym> ccTyVars = FreeVarSymCollector.applyTo(cc.getType());
                if (ccTyVars.contains(tyVarSym)) {
                    // remove those constraints that contain the replaced type variable
                    cc_it.remove();
                }
            }

            final Iterator<HaskellSubstitution> it = ((TyCaseAnnotation) node.getAnnotation()).getTySubstitutions().iterator();
            for (final NarrowNode child : node.getChildren()) {
                final Set<ClassConstraint> newCCs = new HashSet<ClassConstraint>(baseCCs);
                newCCs.addAll(child.getConstraints());
                this.modules.getCcg().reduce(newCCs);

                this.buildCallsWithConstraints(tySubs.combineWith(it.next()), subs, child, target, scc,
                    usableFunctions, false, newCCs);
            }
            return;
        }
        case INSTANCE: {

            // check whether this Instance node exists at all
            if (!this.bic.hasBasicInstance(node.getConstraints())) {
                // we cannot guarantee the existance of this node => do not include this DP
                return;
            }

            for (final NarrowNode child : node.getChildren()) {
                // TODO: maybe a bug????????????????????????????????????????????????????????????????????????
                final Tag tag = (Tag) node.getTag();
                if (tag.getVarExpFreeAppPred()) {
                    // A child is a predecessor of a VarExp- or ParSplit(Var)-node => we cannot include this DP
                    return;
                }
            }

            final InstanceAnnotation instanceAnnotation = (InstanceAnnotation) node.getAnnotation();
            final NarrowNode baseNarrowNode = instanceAnnotation.getBase();
            final boolean onScc = scc.contains(baseNarrowNode);
            final List<NarrowNode> rheads = new Vector<NarrowNode>();
            if (onScc) {
                this.buildTermsWithConstraints(tySubs, subs, node, target, false, NarrowingGraphAnalyser.DPsReplacer, false, rheads, ccs);
            }
            for (final NarrowNode child : node.getChildren()) {
                //this.buildCalls(tySubs,subs,child,target,scc,usableFunctions,false);
                if (onScc) {
                    this.collectUseableFunctions(child, usableFunctions);
                }
            }
            usableFunctions.addAll(rheads);
            return;
        }
        case FIRST:
        case PROGERROR:
        default:
            return;
        }
    }

    /**
     * Builds terms with the class constraints attached to them
     * @param tySubs The current type substitution on the path
     * @param subs The current term substitution on the path
     * @param node The current node
     * @param target Output; will contain triples of a type substition, a term substitution, and a right hand side for rule paths
     * @param head Whether we are a starting point for a rule
     * @param replacer What type of rule shall be built (either DPs or Rules)
     * @param para Whether we are in an argument (PARAmeter) of another term
     * @param rheads Output; collects the nodes from which further rules have to be created
     * @param ccs The Class Constraints that have to be considered
     */
    private void buildTermsWithConstraints(final HaskellSubstitution tySubs,
        final HaskellSubstitution subs,
        final NarrowNode node,
        final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> target,
        final boolean head,
        int replacer,
        final boolean para,
        final List<NarrowNode> rheads,
        final Set<ClassConstraint> ccs) {
        final boolean varExpPredOrFreeAppPred = this.isVarExpFreeAppPred(node);
        if (node.isRoot()) {
            if (!head) {
                if (para && varExpPredOrFreeAppPred) {
                    this.addVar(target, tySubs, subs, node);
                    return;
                }
                HaskellExp baseReplace = this.buildReplaceFor(replacer, node);
                baseReplace = new Apply(baseReplace, this.buildClassConstraintTerm(ccs));
                target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, baseReplace));
                return;
            }
        }
        switch (node.getMode()) {
        case NON: {
            if (para && varExpPredOrFreeAppPred) {
                this.addVar(target, tySubs, subs, node);
                return;
            }
            if (node.getChildren() != null) {
                for (final NarrowNode child : node.getChildren()) {
                    // Do not remove constraints, since we are not sure whether these can be fulfilled
                    this.buildTermsWithConstraints(tySubs, subs, child, target, false, replacer, para, rheads, ccs);
                }
            }
            return;
        }

        case CASE: {
            if (para) {
                if (varExpPredOrFreeAppPred) {
                    this.addVar(target, tySubs, subs, node);
                    return;
                }
                HaskellExp baseReplace = this.buildReplaceFor(replacer, node);
                baseReplace = new Apply(baseReplace, this.buildClassConstraintTerm(ccs));
                // since this is a pseudo-root (we do not have incoming instantiations), we stop here and build a triple
                target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, baseReplace));
                rheads.add(node);
                return;
            }
            final Iterator<HaskellSubstitution> it = ((CaseAnnotation) node.getAnnotation()).getSubstitutions().iterator();
            for (final NarrowNode child : node.getChildren()) {
                final Set<ClassConstraint> newCCs = new HashSet<ClassConstraint>(ccs);
                newCCs.addAll(child.getConstraints());
                this.buildTermsWithConstraints(tySubs, subs.combineWith(it.next()), child, target, false, replacer,
                    para, rheads, newCCs);
            }
            return;
        }

        case TYCASE: {
            if (para) {
                if (varExpPredOrFreeAppPred) {
                    this.addVar(target, tySubs, subs, node);
                    return;
                }
                HaskellExp baseReplace = this.buildReplaceFor(replacer, node);
                baseReplace = new Apply(baseReplace, this.buildClassConstraintTerm(ccs));
                // since this is a pseudo-root (we do not have incoming instantiations), we stop here and build a triple
                target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, baseReplace));
                rheads.add(node);
                return;
            }

            // no children => nothing to do
            if (node.getChildren().isEmpty()) {
                return;
            }

            // Type variables are identified by their HaskellSym, they do not have an entity
            final HaskellSubstitution firstTyCaseSubs = ((TyCaseAnnotation) node.getAnnotation()).getTySubstitutions().get(0);
            final HaskellSym tyVarSym = firstTyCaseSubs.keySet().iterator().next();
            final Set<ClassConstraint> baseCCs = new HashSet<ClassConstraint>(ccs);
            for (final Iterator<ClassConstraint> cc_it = baseCCs.iterator(); cc_it.hasNext();) {
                final ClassConstraint cc = cc_it.next();
                final Set<HaskellSym> ccTyVars = FreeVarSymCollector.applyTo(cc.getType());
                if (ccTyVars.contains(tyVarSym)) {
                    // remove those constraints that contain the replaced type variable
                    cc_it.remove();
                }
            }

            final Iterator<HaskellSubstitution> it = ((TyCaseAnnotation) node.getAnnotation()).getTySubstitutions().iterator();
            for (final NarrowNode child : node.getChildren()) {
                final Set<ClassConstraint> newCCs = new HashSet<ClassConstraint>(baseCCs);
                newCCs.addAll(child.getConstraints());
                this.modules.getCcg().reduce(newCCs);
                this.buildTermsWithConstraints(tySubs.combineWith(it.next()), subs, child, target, false, replacer,
                    para, rheads, newCCs);
            }
            return;
        }

        case VAREXP: {
            /*List<Triple<Substitution,Substitution,HaskellExp>> pbs = new Vector<Triple<Substitution,Substitution,HaskellExp>>();
            NarrowNode baseNarrowNode = node.getChildren().iterator().next();
            this.buildTerms(tySubs,subs,baseNarrowNode,pbs,false,replacer,rheads);
            for (Triple<Substitution,Substitution,HaskellExp> sse : pbs){
                sse.z = (HaskellExp)(((Apply) (sse.z)).getFunction());
                target.add(sse);
            } */

            // was previously:
            //this.addVar(target,tySubs,subs,node);

            // do not add the class constraints, since this will become a constructor in the created DP problem
            final HaskellExp baseReplace = this.buildReplaceFor(replacer, node);
            target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, baseReplace));

            return;
        }

        case CONS: {
            final ConsAnnotation ca = (ConsAnnotation) node.getAnnotation();
            final HaskellObject cBase = ca.getCBase();
            final List<Var> vars = ca.getVars();
            final List<NarrowNode> children = node.getChildren();

            // check, whether this term exists at all
            if (!this.bic.hasBasicInstance(ccs)) {
                // this term has no basic instance. Either we are reading rules, then there will not be a rhs for this term.
                // If we are in a subterm of a rhs of an Ins-node, then we cannot be here, since only Case and TyCase can introduce new
                // class constraints, but these will not be followed (see RTA06, ev(t) = t for a Case/TyCase node t)
                return;
            }

            // since we do not have SCC information available, we collect all the children's class constraints and push them downwards
            final Set<ClassConstraint> newCCs = new HashSet<ClassConstraint>(ccs);
            for (final NarrowNode child : children) {
                newCCs.addAll(child.getConstraints());
            }

            final Collection[] cross = new Collection[children.size()];
            // we use the instance combinator here, since we do not want class constraints inside of constructors
            final InstanceCombinator aCombi =
                new InstanceCombinator((HaskellExp) cBase, vars, tySubs, subs, new HaskellSubstitution());
            int i = 0;
            for (final NarrowNode child : children) {
                final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> pbs =
                    new Vector<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>>();
                this.buildTermsWithConstraints(tySubs, subs, child, pbs, false, replacer, true, rheads, newCCs);
                cross[i] = pbs;
                i++;
            }
            Collection_Util.crossProduct(cross, aCombi, target);
            return;
        }

        case INSTANCE: {
            if (para && varExpPredOrFreeAppPred) {
                this.addVar(target, tySubs, subs, node);
                return;
            }
            final InstanceAnnotation instanceAnnotation = (InstanceAnnotation) node.getAnnotation();
            final NarrowNode baseNarrowNode = instanceAnnotation.getBase();
            final HaskellSubstitution tyMatchSub = instanceAnnotation.getTyMatchSubs();
            final List<Var> vars = instanceAnnotation.getVars();
            final HaskellExp baseReplace = this.buildReplaceFor(replacer, baseNarrowNode);
            final List<NarrowNode> children = node.getChildren();
            final Collection[] cross = new Collection[children.size()];
            final NonTermInstanceCombinator iCombi =
                new NonTermInstanceCombinator(baseReplace, vars, tySubs, subs, tyMatchSub, ccs);
            int i = 0;
            replacer = NarrowingGraphAnalyser.RulesReplacer;
            //HaskellSym.showee(node);
            for (final NarrowNode child : children) {
                final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> pbs =
                    new Vector<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>>();
                this.buildTermsWithConstraints(tySubs, subs, child, pbs, false, replacer, true, rheads,
                    child.getConstraints());
                cross[i] = pbs;
                i++;
            }
            Collection_Util.crossProduct(cross, iCombi, target);
            return;
        }

        case PROGERROR: {
            target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, node.getExpression()));
            return;
        }

        case UNIVAR: {
            if (para && varExpPredOrFreeAppPred) {
                this.addVar(target, tySubs, subs, node);
                return;
            }

            if (!node.getChildren().isEmpty()) {
                // we should never arrive here, since there must not be a ParSplit(Var) in the rules!
                throw new RuntimeException("ParSplit(Var) in NonTerm rules!");
            }

            final Var var = ((UniVarAnnotation) node.getAnnotation()).getVar();
            target.add(new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, var));
            /*
            List<NarrowNode> children = node.getChildren();
            Collection[] cross = new Collection[children.size()];
            ArgumentCombinator aCombi = new ArgumentCombinator(var,tySubs,subs,this);
            int i = 0;
            for (NarrowNode child : children){
                List<Triple<Substitution,Substitution,HaskellExp>> pbs = new Vector<Triple<Substitution,Substitution,HaskellExp>>();
                this.buildTerms(tySubs,subs,child,pbs,false,replacer,true,rheads);
                cross[i] = pbs;
                i++;
            }
            Collection_Util.crossProduct(cross,aCombi,target);
            */
            return;
        }

        case FIRST:
        default:
            //                throw new RuntimeException("incorrect node annotation");
        }
    }

    @Override
    public void buildRulesForNode(final NarrowNode node, final Collection<Pair<HaskellExp, HaskellExp>> target) {
        this.buildRulesForNodeWithConstraints(node, target, node.getConstraints());
    }

    /**
     * Worker function for {@link #buildRulesForNode(NarrowNode, Collection)}.
     * Encodes class constraints into the terms, thus also class constraint reduction rules must be included in the rules.
     * @param node The current node to create rules from.
     * @param target Output; will contain tuples of (lhs and rhs) of rules
     * @param ccs The set of class constraints to consider for this node
     */
    private void buildRulesForNodeWithConstraints(final NarrowNode node,
        final Collection<Pair<HaskellExp, HaskellExp>> target,
        final Set<ClassConstraint> ccs) {
        //HaskellExp oleft = node.getExpression();
        final HaskellExp left = this.buildReplaceFor(NarrowingGraphAnalyser.RulesReplacer, node);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("$RULES$  "+node.num+"---"+left);
        }

        final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> srhss =
            new Vector<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>>();
        final List<NarrowNode> rheads = new Vector<NarrowNode>();
        this.buildTermsWithConstraints(new HaskellSubstitution(), new HaskellSubstitution(), node, srhss, true, NarrowingGraphAnalyser.RulesReplacer, false,
            rheads, ccs);
        for (final Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp> srhs : srhss) {
            HaskellExp lhs = (HaskellExp) srhs.y.applyTo((BasicTerm) left);
            (new TypeAnnotationSubstitutor(srhs.x)).applyTo(lhs);
            //HaskellExp olhs = (HaskellExp) srhs.y.applyTo((BasicTerm)oleft);

            lhs = (HaskellExp) srhs.x.applyTo((BasicTerm) lhs);

            //(new TypeAnnotationSubstitutor(srhs.x)).applyTo(olhs);
            final HaskellExp rhs = srhs.z;

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println(olhs);
                //System.out.println(lhs+" --> "+rhs);
                //System.out.println();
            }

            lhs = new Apply(lhs, new Cons(new HaskellNamedSym(this.listNil)));

            target.add(new Pair<HaskellExp, HaskellExp>(lhs, rhs));
        }
        for (final NarrowNode rhead : rheads) {
            this.buildRulesForNode(rhead, target);
        }
    }

    /**
     * builds a term containing the class constraints surrounded with the ccCheck function, if there is at least one class constraint.
     * @param ccs The set of ClassConstraints to construct a term for
     * @return The Haskell term that can be appended to the term constructed
     */
    private HaskellExp buildClassConstraintTerm(final Set<ClassConstraint> ccs) {
        HaskellExp constraintTerm = new Cons(new HaskellNamedSym(this.listNil));
        for (final ClassConstraint cc : ccs) {
            constraintTerm =
                (HaskellExp) HaskellTools.buildApplies(Arrays.asList((HaskellObject) new Cons(new HaskellNamedSym(
                    this.listCons)), new Apply(new Cons(cc.getTyClass()), cc.getType()), constraintTerm));
            this.ccUsedTyClasses.add((TyClassEntity) cc.getTyClass().getEntity());
        }

        if (!ccs.isEmpty()) {
            if (this.ccCheckEntity == null) {
                final String ccCheckName = this.modules.getPrelude().getFreshNameFor("ccCheck");
                this.ccCheckEntity = new VarEntity(ccCheckName, this.modules.getPrelude(), null, null);
            }
            constraintTerm = new Apply(new Var(new HaskellNamedSym(this.ccCheckEntity)), constraintTerm);
        }

        return constraintTerm;
    }

    private class NonTermInstanceCombinator implements
            Collection_Util.Combinator<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> {
        private final HaskellExp baseReplace;
        private final List<Var> vars;
        private final HaskellSubstitution ptySubs;
        private final HaskellSubstitution psubs;
        private final HaskellSubstitution tyMatchSubs;
        private final Set<ClassConstraint> ccs;

        public NonTermInstanceCombinator(final HaskellExp baseReplace, final List<Var> vars,
                final HaskellSubstitution ptySubs, final HaskellSubstitution psubs, final HaskellSubstitution tyMatchSubs,
                final Set<ClassConstraint> ccs) {
            this.baseReplace = baseReplace;
            this.vars = vars;
            this.ptySubs = ptySubs;
            this.psubs = psubs;
            this.tyMatchSubs = tyMatchSubs;
            this.ccs = ccs;
        }

        @Override
        public Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp> combine(final Object[] objs) {
            int i = 0;
            HaskellSubstitution subs = this.psubs;
            ;
            HaskellSubstitution tySubs = this.ptySubs;
            ;
            final HaskellSubstitution instance = new HaskellSubstitution();
            for (final Var var : this.vars) {
                final Triple triple = (Triple) objs[i];
                tySubs = tySubs.combineWith((HaskellSubstitution) triple.x);
                subs = subs.combineWith((HaskellSubstitution) triple.y);
                final HaskellExp exp = (HaskellExp) triple.z;
                i++;
                instance.put(var.getSymbol(), exp);
            }
            BasicTerm res = Copy.deep((BasicTerm) this.baseReplace);
            (new TypeAnnotationSubstitutor(this.tyMatchSubs)).applyTo(res);
            res = instance.applyTo(res);
            res = subs.applyTo(res);
            (new TypeAnnotationSubstitutor(tySubs)).applyTo(res);
            res = this.tyMatchSubs.applyTo(res);

            final HaskellExp constraintTerm = NarrowingGraphToNonTermDPs.this.buildClassConstraintTerm(this.ccs);

            res = new Apply(res, constraintTerm);

            return new Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>(tySubs, subs, (HaskellExp) res);
        }
    }

}
