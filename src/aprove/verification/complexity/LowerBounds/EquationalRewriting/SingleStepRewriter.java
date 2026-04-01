package aprove.verification.complexity.LowerBounds.EquationalRewriting;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;

public class SingleStepRewriter {

    private LowerBoundsToolbox toolbox;

    public SingleStepRewriter(LowerBoundsToolbox toolbox) {
        this.toolbox = toolbox;
    }

    public Set<RewriteStep> rewrite(TRSTerm term, Position pi) throws AbortionException {
        Set<RewriteStep> res = new LinkedHashSet<>();
        // remember if we weren't able to decide whether some rule was applicable or not
        this.rewriteWithRules(this.toolbox.trs.getRulesToProveLemma(this.toolbox), term, pi, res);
        if (res.isEmpty()) {
            this.rewriteWithRules(this.toolbox.trs.getIndefiniteLemmas(this.toolbox), term, pi, res);
        }
        return res;
    }

    private void rewriteWithRules(List<AbstractRule> rules, TRSTerm t, Position pi, Set<RewriteStep> res) {
        TRSTerm s = t.getSubterm(pi);
        for (AbstractRule rule : rules) {
            TRSSubstitution sigma = this.toolbox.unifier.match(rule.getLeft(), s);
            if (sigma == null) {
                continue;
            }
            TRSTerm newS = rule.getRight().applySubstitution(sigma);
            if (this.toolbox.pfHelper.normalize(s).equals(this.toolbox.pfHelper.normalize(newS))) {
                continue;
            }
            res.add(new RewriteStep(rule, t, pi, sigma));
        }
    }

}
