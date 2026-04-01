package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * @author Stephan Swiderski
 */

public class NarrowingGraphToDPs extends NarrowingGraphToRules {

    public NarrowingGraphToDPs(final Modules modules, final NarrowNode freeAppNode) {
        super(modules, freeAppNode);
    }

    public void buildCalls(
        final HaskellSubstitution tySubs,
        final HaskellSubstitution subs,
        final NarrowNode node,
        final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> target,
        final Collection<NarrowNode> scc,
        final Collection<NarrowNode> usableFunctions,
        final boolean head)
    {
        switch (node.getMode()) {
        case NON:
        case VAREXP:
        case UNIVAR:
        case CONS:
            if (node.getChildren() != null) {
                for (final NarrowNode child : node.getChildren()) {
                    this.buildCalls(tySubs, subs, child, target, scc, usableFunctions, false);
                }
            }
            return;
        case CASE: {
            final Iterator<HaskellSubstitution> it = ((CaseAnnotation) node.getAnnotation()).getSubstitutions().iterator();
            for (final NarrowNode child : node.getChildren()) {
                this.buildCalls(tySubs, subs.combineWith(it.next()), child, target, scc, usableFunctions, false);
            }
            return;
        }
        case TYCASE: {
            final Iterator<HaskellSubstitution> it = ((TyCaseAnnotation) node.getAnnotation()).getTySubstitutions().iterator();
            for (final NarrowNode child : node.getChildren()) {
                this.buildCalls(tySubs.combineWith(it.next()), subs, child, target, scc, usableFunctions, false);
            }
            return;
        }
        case INSTANCE: {
            final InstanceAnnotation instanceAnnotation = (InstanceAnnotation) node.getAnnotation();
            final NarrowNode baseNarrowNode = instanceAnnotation.getBase();
            final boolean onScc = scc.contains(baseNarrowNode);
            final List<NarrowNode> rheads = new Vector<NarrowNode>();
            if (onScc) {
                this.buildTerms(tySubs, subs, node, target, false, NarrowingGraphAnalyser.DPsReplacer, false, rheads);
            }
            for (final NarrowNode child : node.getChildren()) {
                this.buildCalls(tySubs, subs, child, target, scc, usableFunctions, false);
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

    public void buildDPGraph(NarrowNode root, final NarrowNode node, final Graph<NarrowNode, Object> target) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("CurrentA: "+node+" root "+root);
        }

        final boolean visited = (node.getMark() == target);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("CurrentB: "+node);
        }

        node.setMark(target);
        if (!visited) {
            target.addNode(new Node<NarrowNode>(node));
        }
        if (node.isRoot()) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("SCCGraph: "+node);
            }

            if (root != null) {
                final Node<NarrowNode> rnode = target.getNodeFromObject(root);
                final Node<NarrowNode> nnode = target.getNodeFromObject(node);
                target.addEdge(rnode, nnode);

                // XXX DEBUG
                if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                    //System.out.println(root+" --- "+node);
                }
            }
            root = node;
        }
        if (visited) {
            return;
        }
        if (node.getMode() == Mode.INSTANCE) {
            final InstanceAnnotation instanceAnnotation = (InstanceAnnotation) node.getAnnotation();
            this.buildDPGraph(root, instanceAnnotation.getBase(), target);
        }
        if (node.getChildren() != null) {
            for (final NarrowNode child : node.getChildren()) {
                this.buildDPGraph(root, child, target);
            }
        }
    }

    public List<HaskellPR> buildDPs(final NarrowNode tree) {
        final List<HaskellPR> hprs = new Vector<HaskellPR>();
        final Graph<NarrowNode, Object> graph = new Graph<NarrowNode, Object>();
        this.buildDPGraph(null, tree, graph);
        int j = 0;
        for (final Cycle<NarrowNode> scc : graph.getSCCs()) {
            final List<Pair<HaskellExp, HaskellExp>> dps = new Vector<Pair<HaskellExp, HaskellExp>>();
            final List<Pair<HaskellExp, HaskellExp>> rules = new Vector<Pair<HaskellExp, HaskellExp>>();
            final Set<NarrowNode> usableFunctions = new HashSet<NarrowNode>();
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
            hprs.add(new HaskellPR(dps, rules));
        }
        return hprs;
    }

    public void buildDPsForNode(
        final NarrowNode node,
        final Collection<Pair<HaskellExp, HaskellExp>> target,
        final Set<NarrowNode> scc,
        final Set<NarrowNode> usableFunctions)
    {
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

            target.add(new Pair<HaskellExp, HaskellExp>(lhs, rhs));
        }
    }

    public void buildDPsForSCC(
        final Set<NarrowNode> scc,
        final Collection<Pair<HaskellExp, HaskellExp>> target,
        final Set<NarrowNode> usableFunctions)
    {
        for (final NarrowNode node : scc) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("Build DPs for: "+node);
            }

            this.buildDPsForNode(node, target, scc, usableFunctions);
        }
    }

    public void collectUseableFunctions(final NarrowNode node, final Collection<NarrowNode> target) {
        if (target.contains(node) || this.isVarExpFreeAppPred(node) || (node.getMode() == Mode.VAREXP)) {
            return;
        }
        if (node.getMode() == Mode.VAREXP) {
            return;
        }
        if (node.isRoot()) {
            target.add(node);
        }
        if (node.getMode() == Mode.INSTANCE) {
            final InstanceAnnotation instanceAnnotation = (InstanceAnnotation) node.getAnnotation();
            this.collectUseableFunctions(instanceAnnotation.getBase(), target);
        }
        if (node.getChildren() != null) {
            for (final NarrowNode child : node.getChildren()) {
                this.collectUseableFunctions(child, target);
            }
        }
    }

    public List<HaskellPR> dpAnalyse(final NarrowNode tree) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("######## ****** Loop was legaly leaved");
        }

        // if the node limit was reached, return null right away, avoiding NullPointerException
        if (tree == null) {
            return null;
        }

        this.markVarExpFreeAppPreds(tree);
        final String s = this.buildDOT(tree);
        this.graph = s;
        return this.buildDPs(tree);
    }
}
