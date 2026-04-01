package aprove.verification.complexity.LowerBounds.EquationalRewriting;

import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public class SingleStepNarrower {

    private LowerBoundsToolbox toolbox;

    public SingleStepNarrower(LowerBoundsToolbox toolbox) {
        this.toolbox = toolbox;
    }

    public Set<RewriteStep> rewrite(TRSTerm t, Position pi) {
        TRSTerm s = t.getSubterm(pi);
        List<AbstractRule> filteredRules = this.filterRules(s);
        Set<RewriteStep> res = this.rewriteWithRules(t, pi, filteredRules);
        if (res.isEmpty()) {
            res = this.rewriteWithRules(t, pi, this.alternativeRules(s, filteredRules));
            if (res.isEmpty()) {
                res = this.rewriteWithRules(t, pi, this.toolbox.trs.getIndefiniteLemmas(this.toolbox));
            }
        }
        return res;
    }

    private Set<RewriteStep> rewriteWithRules(TRSTerm t, Position pi, List<AbstractRule> rules) {
        TRSTerm s = t.getSubterm(pi);
        Set<RewriteStep> res = new LinkedHashSet<>();
        RuleLoop: for (AbstractRule r : rules) {
            AbstractRule rule = r.renameVariables(this.toolbox.renamingCentral, this.toolbox.trs.getTypes());
            TRSSubstitution sigma = this.toolbox.unifier.unify(rule.getLeft(), s);
            if (sigma == null) {
                continue;
            }
            TRSTerm news = rule.getRight().applySubstitution(sigma);
            if (this.toolbox.pfHelper.normalize(s).equals(this.toolbox.pfHelper.normalize(news))) {
                continue RuleLoop;
            }
            res.add(new RewriteStep(rule, t, pi, sigma));
        }
        return res;
    }

    private List<AbstractRule> alternativeRules(TRSTerm s, List<AbstractRule> filteredRules) {
        if (s.isVariable()) {
            return Collections.emptyList();
        }
        List<AbstractRule> res = new ArrayList<>();
        res.addAll(this.toolbox.trs.getRulesToProveLemma(this.toolbox));
        res.removeAll(filteredRules);
        Iterator<AbstractRule> it = res.iterator();
        FunctionSymbol root = ((TRSFunctionApplication)s).getRootSymbol();
        while(it.hasNext()) {
            if (!it.next().getRootSymbol().equals(root)) {
                it.remove();
            }
        }
        return res;
    }

    private List<AbstractRule> filterRules(TRSTerm s) {
        if (s.isVariable()) {
            return Collections.emptyList();
        }
        List<AbstractRule> filtered = new ArrayList<>();
        for (AbstractRule r : this.toolbox.trs.getRulesToProveLemma(this.toolbox)) {
            if (r.getRootSymbol().equals(((TRSFunctionApplication) s).getRootSymbol())) {
                filtered.add(r);
            }
        }
        filtered = this.forceLemmata(filtered);
        Set<List<AbstractRule>> res = this.constructNonOverlappingSubsets(filtered);
        return this.largest(res);
    }

    private List<AbstractRule> forceLemmata(List<AbstractRule> filtered) {
        if (filtered.stream().anyMatch(x -> x instanceof Lemma)) {
            return filtered.stream().filter(x -> x instanceof Lemma).collect(toList());
        } else {
            return filtered;
        }
    }

    private Set<List<AbstractRule>> constructNonOverlappingSubsets(List<AbstractRule> filtered) {
        Set<List<AbstractRule>> res = new LinkedHashSet<>();
        for (AbstractRule r : filtered) {
            Set<List<AbstractRule>> toAdd = new LinkedHashSet<>();
            for (List<AbstractRule> resCandidate : res) {
                if (!this.overlapps(r, resCandidate)) {
                    toAdd.add(new ArrayList<>(resCandidate));
                    resCandidate.add(r);
                }
            }
            List<AbstractRule> singleton = new ArrayList<>();
            singleton.add(r);
            toAdd.add(singleton);
            res.addAll(toAdd);
        }
        return res;
    }

    private boolean overlapps(AbstractRule r, List<AbstractRule> resCandidate) {
        for (AbstractRule or : resCandidate) {
            if (r.renameVariables(this.toolbox.renamingCentral, this.toolbox.types).getLeft().unifies(or.getLeft())) {
                return true;
            }
        }
        return false;
    }

    private List<AbstractRule> largest(Set<List<AbstractRule>> res) {
        List<AbstractRule> max = Collections.emptyList();
        for (List<AbstractRule> resCandidate : res) {
            if (resCandidate.size() > max.size()) {
                max = resCandidate;
            } else if (resCandidate.size() == max.size() && this.numberOfRecursiveRules(resCandidate) > this.numberOfRecursiveRules(max)) {
                max = resCandidate;
            }
        }
        return max;
    }

    private int numberOfRecursiveRules(List<AbstractRule> rules) {
        int res = 0;
        for (AbstractRule r : rules) {
            if (this.toolbox.trs.getDependencyGraph().isRecursive(r)) {
                res++;
            }
        }
        return res;
    }

}
