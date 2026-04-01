package aprove.verification.complexity.LowerBounds.BasicStructures;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class LowerBoundsTrs extends TypedTrs {

    private Map<FunctionSymbol, Lemma> lemmas = new LinkedHashMap<>();
    private InductionHypothesis inductionHypothesis;

    public LowerBoundsTrs(Set<Rule> rules, TrsTypes types, boolean innermost) {
        super(rules, types, innermost);
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder sb = new StringBuilder(super.export(eu));
        if (!this.lemmas.isEmpty()) {
            sb.append(eu.paragraph());
            sb.append("Lemmas:");
            sb.append(eu.linebreak());
            for (AbstractRule r : this.lemmas.values()) {
                sb.append(eu.export(r));
                sb.append(eu.linebreak());
            }
        }
        return sb.toString();
    }

    public YNM unifiesWithLhs(TRSFunctionApplication s, LowerBoundsToolbox toolbox) {
        List<Rule> allRules = new ArrayList<>(this.getRules().size());
        allRules.addAll(this.getRules());
        Type sType = toolbox.types.getReturnType(s.getRootSymbol());
        for (Rule rule : allRules) {
            Type t = toolbox.types.getReturnType(rule.getRootSymbol());
            if (!sType.equals(t)) {
                continue;
            }
            if (toolbox.unifier.unify(rule.getLeft(), s) != null) {
                return YNM.YES;
            }
        }
        return YNM.NO;
    }

    public void add(Lemma lemma) {
        this.lemmas.put(lemma.getRootSymbol(), lemma);
    }

    public Lemma getMostExpensiveLemma() {
        Lemma res = null;
        ComplexityValue complexity = null;
        for (Lemma lemma: this.lemmas.values()) {
            ComplexityValue newComplexity = lemma.getIrc(this.getTypes());
            if (res == null || complexity.compareTo(newComplexity) < 0) {
                res = lemma;
                complexity = newComplexity;
            }
        }
        return res;
    }

    public List<AbstractRule> getRulesToProveLemma(LowerBoundsToolbox toolbox) {
        List<AbstractRule> allRules = new ArrayList<>();
        if (this.inductionHypothesis != null) {
            allRules.add(this.inductionHypothesis);
        }
        for (Entry<FunctionSymbol, Lemma> e: this.lemmas.entrySet()) {
            FunctionSymbol g = e.getKey();
            Lemma lemma = e.getValue();
            if (!toolbox.toAnalyze.equals(g) && !lemma.isIndefinite(toolbox) && !lemma.getComplexity().isExponential()) {
                allRules.add(e.getValue());
            }
        }
        allRules.addAll(this.getRules());
        return allRules;
    }

    public ComplexityValue getComplexity() {
        Lemma lemma = this.getMostExpensiveLemma();
        if (lemma == null) {
            return ComplexityValue.constant();
        } else {
            return lemma.getIrc(this.getTypes());
        }
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public void setInductionHypothesis(InductionHypothesis inductionHypothesis) {
        this.inductionHypothesis = inductionHypothesis;
    }

    public void removeInductionHypothesis() {
        this.inductionHypothesis = null;
    }

    @Override
    public LowerBoundsTrs clone() {
        LowerBoundsTrs res = new LowerBoundsTrs(new LinkedHashSet<>(this.getRules()), this.getTypes().clone(), this.isInnermost());
        res.lemmas.putAll(this.lemmas);
        return res;
    }

    public int recursiveCallsOnArguments(FunctionSymbol c, int i) {
        int res = 0;
        RULE: for (AbstractRule r: this.getRules()) {
            TRSFunctionApplication lhs = r.getLeft();
            TRSTerm rhs = r.getRight();
            for (Pair<Position, TRSTerm> p1: lhs.getPositionsWithSubTerms()) {
                Position pi = p1.x;
                if (pi.isEmptyPosition() || p1.y.isVariable()) {
                    continue;
                }
                TRSFunctionApplication t = (TRSFunctionApplication) p1.y;
                if (t.getRootSymbol().equals(c)) {
                    // We found c on the lhs at position pi.
                    TRSTerm arg = t.getArgument(i);
                    FunctionSymbol f = null;
                    Position tau;
                    for (tau = pi.shorten(1); tau != null; tau = tau.isEmptyPosition() ? null : tau.shorten(1)) {
                        TRSTerm s = lhs.getSubterm(tau);
                        if (s.isVariable()) {
                            continue;
                        }
                        FunctionSymbol g = ((TRSFunctionApplication)s).getRootSymbol();
                        if (this.getDefinedSymbols().contains(g)) {
                            // We found the innermost defined symbol above this occurrence of c.
                            f = g;
                            break;
                        }
                    }
                    if (f != null) {
                        for (Pair<Position, TRSTerm> p2: rhs.getPositionsWithSubTerms()) {
                            Position mu = p2.x;
                            TRSTerm p = p2.y;
                            if (!mu.isEmptyPosition() && p.equals(arg)) {
                                // We found the argument of c we are looking for on the rhs.
                                for (Position nu = mu.shorten(1); nu != null; nu = nu.isEmptyPosition() ? null : nu.shorten(1)) {
                                    TRSTerm q = rhs.getSubterm(nu);
                                    if (q.isVariable()) {
                                        continue;
                                    }
                                    FunctionSymbol g = ((TRSFunctionApplication)q).getRootSymbol();
                                    if (g.equals(f)) {
                                        // The argument of c we are looking for is nested in a recursive call of f.
                                        res++;
                                        continue RULE;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return res;
    }

    public int numberOfLemmas() {
        return this.lemmas.size();
    }

    public List<AbstractRule> getIndefiniteLemmas(LowerBoundsToolbox toolbox) {
        List<AbstractRule> res = new ArrayList<>();
        for (Lemma l: this.lemmas.values()) {
            if (l.isIndefinite(toolbox)) {
                res.add(l);
            }
        }
        return res;
    }
}
