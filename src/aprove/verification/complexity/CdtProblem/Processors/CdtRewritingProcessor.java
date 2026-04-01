package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CdtProblem.Utils.*;
import aprove.verification.complexity.CdtProblem.Utils.IcapCalculator;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class CdtRewritingProcessor extends CdtTransformationProcessor{

    @ParamsViaArgumentObject
    public CdtRewritingProcessor(Arguments args) {
        super(args);
    }

    @Override
    protected Transformation computeTransformation(State st, Node<Cdt> node) {
        UsableRulesCalculator urCalc= st.cdtProblem.getURCalc();
        IcapCalculator icap = st.cdtGraph.getIcap();
        Cdt nodeCdt = icap.renameVarDisjoint(node.getObject());

        Set<Rule> usableRules = urCalc.estimateUsableRules(nodeCdt.getRule());
        Cdt rewrittenCdt = this.doRewriting(nodeCdt, urCalc, usableRules);
        if (rewrittenCdt == null) {
            return null;
        } else {
            Transformation result = new Transformation(false,
                    GraphHistory.Technique.Rewriting,
                    node, Collections.singleton(rewrittenCdt),
                    new CdtRewritingProof(node.getObject(), rewrittenCdt));
            return result;
        }
    }

    private boolean isNonOverlapping(Set<Rule> rules) {
        AbortableIterator<ImmutableTriple<TRSTerm, TRSTerm, Boolean>> critPairIter =
            GeneralizedRule.getCriticalPairs(rules);
        try {
            // XXX - use the real Abortion here!
            // Propagate it into here somehow if we need to.
            if (!critPairIter.hasNext(AbortionFactory.create())) {
                /* rsRules are non-overlapping */
                return true;
            }
        } catch (AbortionException e) {
            // should never happen.
        }
        return false;
    }

    private Cdt doRewriting(Cdt nodeCdt,
            UsableRulesCalculator urCalc, Set<Rule> rules) {

        for (TermIterator it = new TermIterator(nodeCdt.getRuleRHS()); it.hasNext();) {
            TermIterator.Entry e = it.next();
            TRSTerm t = e.getTerm();
            Position p = e.getPosition();
            if (t.isVariable() || p.getDepth() == 1) {
                continue;
            }

            TRSFunctionApplication fa = (TRSFunctionApplication)t;
            for (Rule r : rules) {
                TRSSubstitution matcher = r.getLeft().getMatcher(fa);
                if (matcher != null) {
                    Set<Rule> usableRules = urCalc.estimateUsableRules(
                            Rule.create(nodeCdt.getRuleLHS(), t));
                    if (this.isNonOverlapping(usableRules)) {
                        TRSTerm substRhs = r.getRight().applySubstitution(matcher);
                        TRSTerm rewrittenRhs =
                            nodeCdt.getRuleRHS().replaceAt(p, substRhs);
                        return Cdt.create(Rule.create(nodeCdt.getRuleLHS(), rewrittenRhs));
                    }
                }
            }
        }
        return null;
    }

    static class CdtRewritingProof extends CpxProof {

        private final Cdt oldCdt;
        private final Cdt newCdt;

        public CdtRewritingProof(Cdt oldCdt, Cdt newCdt) {
            this.oldCdt = oldCdt;
            this.newCdt = newCdt;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append(o.escape("Used rewriting to replace "));
            sb.append(o.export(this.oldCdt));
            sb.append(o.escape(" by "));
            sb.append(o.export(this.newCdt));
            return sb.toString();
        }

    }
}
