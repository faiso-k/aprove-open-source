package aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/** A sequence of rewrite steps, together with lots of additional information. */
public class RewriteSequence implements Iterable<RewriteStep>, Exportable {

    private TRSFunctionApplication startTerm;
    protected List<RewriteStep> steps;
    protected LowerBoundsToolbox toolbox;
    private TRSTerm res;
    private TRSTerm resRL;
    private TRSSubstitution sigma;

    protected RewriteSequence(TRSFunctionApplication startTerm,
            List<RewriteStep> steps,
            LowerBoundsToolbox toolbox) {
        super();
        this.startTerm = startTerm;
        this.steps = steps;
        this.toolbox = toolbox;
    }

    public RewriteSequence(TRSFunctionApplication startTerm, LowerBoundsToolbox toolbox) {
        this(startTerm, new ArrayList<>(), toolbox);
    }

    public RewriteSequence addStep(RewriteStep s) {
        List<RewriteStep> newSteps = new ArrayList<>(this.steps);
        newSteps.add(s);
        return new RewriteSequence(this.startTerm, newSteps, this.toolbox);
    }

    public TRSTerm getResult() {
        if (this.res == null) {
            this.res = this.steps.isEmpty() ? this.startTerm : this.toolbox.pfHelper.normalize(this.steps.get(this.steps.size() - 1).getResult());
        }
        return this.res;
    }

    public TRSTerm getResultRL() {
        if (this.resRL == null) {
            this.resRL = this.toolbox.genEqRewriter.normalizeRL(this.getResult());
        }
        return this.resRL;
    }

    public boolean isEmpty() {
        return this.steps.isEmpty();
    }

    public int size() {
        return this.steps.size();
    }

    public TRSFunctionApplication getStartTerm() {
        return this.startTerm;
    }

    @Override
    public RewriteSequence clone() {
        List<RewriteStep> newSteps = new ArrayList<>(this.steps);
        return new RewriteSequence(this.startTerm, newSteps, this.toolbox);
    }

    @Override
    public String toString() {
        return this.startTerm.applySubstitution(this.composeSubstitutions()).toString() + " ->* " + this.getResult();
    }

    public TRSSubstitution composeSubstitutions() {
        if (this.sigma == null) {
            this.sigma = TRSSubstitution.EMPTY_SUBSTITUTION;
            for (RewriteStep step : this) {
                this.sigma = this.sigma.compose(step.getSigma().restrictTo(step.getOldTerm().getVariables()));
            }
            // normalize the terms
            for (TRSVariable var : this.sigma.getVariables()) {
                TRSTerm t = this.sigma.substitute(var);
                this.sigma = this.sigma.remove(var);
                this.sigma = this.sigma.extend(TRSSubstitution.create(var, this.toolbox.pfHelper.normalize(t)));
            }
        }
        return this.sigma;
    }

    @Override
    public Iterator<RewriteStep> iterator() {
        return this.steps.iterator();
    }

    @Override
    public String export(Export_Util eu) {
        String res = eu.export(this.startTerm);
        for (RewriteStep step: this.steps) {
            res += eu.appSpace();
            res += eu.rightarrow();
            res += eu.sub(eu.escape(step.getRule().getIndex()));
            Complexity complexity = step.getComplexity(this.toolbox);
            if (!complexity.isUnknown()) {
                res += eu.sup(eu.Omega() + eu.escape("(") + step.getComplexity(this.toolbox).export(eu) + eu.escape(")"));
            }
            res += eu.linebreak();
            res += step.getResult().export(eu);
        }
        return res;
    }

    public boolean applied(AbstractRule r) {
        BidirectionalMap<TRSVariable, TRSVariable> map = TermNormalization.getRenamingMapForVariables(r.getLeft(), r.getRight());
        TRSTerm lNorm = r.getLeft().renameVariables(map.getLRMap());
        TRSTerm rNorm = r.getRight().renameVariables(map.getLRMap());
        for (RewriteStep s: this) {
            AbstractRule or = s.getRule();
            BidirectionalMap<TRSVariable, TRSVariable> omap = TermNormalization.getRenamingMapForVariables(or.getLeft(), or.getRight());
            TRSTerm olNorm = or.getLeft().renameVariables(omap.getLRMap());
            TRSTerm orNorm = or.getRight().renameVariables(omap.getLRMap());
            if (olNorm.equals(lNorm) && orNorm.equals(rNorm)) {
                return true;
            }
        }
        return false;
    }

    public RewriteSequence replaceAll(Map<TRSTerm, TRSTerm> map) {
        TRSFunctionApplication newStartTerm = (TRSFunctionApplication) this.startTerm.replaceAll(map);
        List<RewriteStep> newSteps = new ArrayList<>();
        for (RewriteStep step: this.steps) {
            newSteps.add(step.replaceAll(map));
        }
        return new RewriteSequence(newStartTerm, newSteps, this.toolbox);
    }

    public Set<AbstractRule> getRules() {
        Set<AbstractRule> res = new LinkedHashSet<>();
        for (RewriteStep s : this) {
            res.add(s.getRule());
        }
        return res;
    }

    public BigInteger getRecursionDepth() {
        BigInteger res = this.getRecursionDepth(this.steps, Position.EPSILON);
        /*
         * Intuition: If no non recursive rules for the root symbol of the start term (f) were used,
         * then f most likely calls a helper function (g) with recursive and non-recursive cases.
         * Thus, the last application of a recursive rule for f leads to a base case of g and hence
         * should not be counted as a loop.
         */
        if (this.getBaseCaseRules().isEmpty()) {
            return res.subtract(BigInteger.ONE);
        } else {
            return res;
        }
    }

    private BigInteger getRecursionDepth(List<RewriteStep> subSeq, Position previouslyReducedPos) {
        BigInteger max = BigInteger.ZERO;
        Set<Position> finishedPositions = new LinkedHashSet<>();
        OUTER: for (int i = 0; i < subSeq.size(); i++) {
            RewriteStep step = subSeq.get(i);
            Position reducedPos = step.getPi();
            // are we in the right branch?
            if (previouslyReducedPos.isPrefixOf(reducedPos)) {
                for (Position finishedPos : finishedPositions) {
                    if (finishedPos.isPrefixOf(reducedPos)) {
                        continue OUTER;
                    }
                }
                finishedPositions.add(reducedPos);
                BigInteger current = this.getRecursionDepth(subSeq.subList(i + 1, subSeq.size()), reducedPos);
                if (this.isRecursive(step) && this.reducesStartSymbol(step)) {
                    current = current.add(BigInteger.ONE);
                }
                if (current.compareTo(max) > 0) {
                    max = current;
                }
            }
        }
        return max;
    }

    private Set<AbstractRule> getBaseCaseRules() {
        Set<AbstractRule> res = new LinkedHashSet<>();
        for (RewriteStep step : this) {
            if (this.reducesStartSymbol(step) && !this.isRecursive(step)) {
                res.add(step.getRule());
            }
        }
        return res;
    }

    public boolean hasLoops() {
        for (RewriteStep step : this) {
            if (this.reducesStartSymbol(step) && this.isRecursive(step)) {
                return true;
            }
        }
        return false;
    }

    private boolean isRecursive(RewriteStep step) {
        return this.toolbox.trs.getDependencyGraph().isRecursive(step.getRule());
    }

    private boolean reducesStartSymbol(RewriteStep step) {
        return this.getStartTerm().getRootSymbol().equals(step.getRule().getRootSymbol());
    }

    public RewriteStep getLast() {
        return this.steps.get(this.steps.size() - 1);
    }

    public TRSFunctionApplication getLhs() {
        return this.getStartTerm().applySubstitution(this.composeSubstitutions());
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.startTerm == null) ? 0 : this.startTerm.hashCode());
        result = prime * result + ((this.steps == null) ? 0 : this.steps.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        RewriteSequence other = (RewriteSequence) obj;
        if (this.startTerm == null) {
            if (other.startTerm != null) {
                return false;
            }
        } else if (!this.startTerm.equals(other.startTerm)) {
            return false;
        }
        if (this.steps == null) {
            if (other.steps != null) {
                return false;
            }
        } else if (!this.steps.equals(other.steps)) {
            return false;
        }
        return true;
    }
}
