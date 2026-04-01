package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 */

public class NarrowingGraphToRules extends NarrowingGraphToDOT {

    public NarrowingGraphToRules(final Modules modules, final NarrowNode freeAppNode) {
        super(modules, freeAppNode);
    }

    public List<Pair<HaskellExp, HaskellExp>> analyse(final NarrowNode tree) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("######## ****** Loop was legaly leaved");
        }

        final String s = this.buildDOT(tree);
        this.graph = s;
        return this.getRules(tree);
    }

    public void buildRulesForNode(final NarrowNode node, final Collection<Pair<HaskellExp, HaskellExp>> target) {
        final HaskellExp oleft = node.getExpression();
        final HaskellExp left = this.buildReplaceFor(NarrowingGraphAnalyser.RulesReplacer, node);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("$RULES$  "+node.num+"---"+left);
        }

        final List<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>> srhss =
            new Vector<Triple<HaskellSubstitution, HaskellSubstitution, HaskellExp>>();
        final List<NarrowNode> rheads = new Vector<NarrowNode>();
        this.buildTerms(
            new HaskellSubstitution(),
            new HaskellSubstitution(),
            node,
            srhss,
            true,
            NarrowingGraphAnalyser.RulesReplacer,
            false,
            rheads);
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
                //System.out.println(lhs+" --> "+rhs);
                //System.out.println();
            }

            target.add(new Pair<HaskellExp, HaskellExp>(lhs, rhs));
        }
        for (final NarrowNode rhead : rheads) {
            this.buildRulesForNode(rhead, target);
        }
    }

    public List<Pair<HaskellExp, HaskellExp>> getRules(final NarrowNode tree) {
        final List<Pair<HaskellExp, HaskellExp>> rules = new Vector<Pair<HaskellExp, HaskellExp>>();
        final Iterator<NarrowNode> it = new TreeIterator(tree, true);
        while (it.hasNext()) {
            final NarrowNode node = it.next();
            if (node.isRoot()) {
                this.buildRulesForNode(node, rules);
            }
        }
        return rules;
    }

}
