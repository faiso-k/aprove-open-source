package aprove.verification.complexity.CpxTrsProblem.Processors;

import static aprove.verification.dpframework.BasicStructures.TRSTerm.*;
import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.Processors.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * According to Lemma 49 from our JAR-paper on Lowerbounds of Term Rewriting, termination of
 * narrowing on basic terms implies constant runtime complexity.
 */
public class RuntimeComplexityTrsNarrowingTerminationProcessor extends RuntimeComplexityRelTrsProcessor {

    @Override
    protected boolean isRuntimeComplexityRelTrsApplicable(RuntimeComplexityRelTrsProblem obl) {
        if (Options.certifier != Certifier.NONE) {
            return false;
        }
        TruthValue tv = obl.getTruthValue();
        if (tv instanceof ComplexityYNM && !((ComplexityYNM)tv).getLowerBound().isConstant()) {
            return false;
        }
        return true;
    }

    @Override
    protected Result processRuntimeComplexityRelTrs(RuntimeComplexityRelTrsProblem cpxTrs, Abortion aborter) {
        boolean innermost = cpxTrs.getRewriteStrategy() != RewriteStrategy.FULL;
        Set<FunctionSymbol> definedSymbols = cpxTrs.getDefinedSymbols();
        Set<RewriteSeq> todo = new LinkedHashSet<>();
        for (FunctionSymbol f: definedSymbols) {
            List<TRSTerm> args = new ArrayList<>();
            for (int i = 0; i < f.getArity(); i++) {
                args.add(createVariable("x" + i));
            }
            TRSFunctionApplication t = createFunctionApplication(f, args);
            todo.add(new RewriteSeq(t, Collections.emptyList()));
        }
        Set<RewriteSeq> seqs = narrow(cpxTrs, aborter, innermost, todo, definedSymbols);
        return ResultFactory.provedWithValue(ComplexityYNM.CONSTANT, new NarrowingOnBasicTermsTerminatesProof(seqs));
    }

    static class RewriteStep {

        Position pi;
        TRSFunctionApplication lhs;
        TRSFunctionApplication rhs;

        public RewriteStep(Position pi, TRSFunctionApplication lhs, TRSFunctionApplication rhs) {
            this.pi = pi;
            this.lhs = lhs;
            this.rhs = rhs;
        }

        boolean isInnermost(Set<Rule> rules) {
            TRSTerm redex = lhs.getSubterm(pi);
            for (Pair<?, TRSFunctionApplication> p: redex.getNonRootNonVariablePositionsWithSubTerms()) {
                TRSFunctionApplication t = p.y;
                for (Rule r: rules) {
                    if (r.getLeft().matches(t)) {
                        return false;
                    }
                }
            }
            return true;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
            result = prime * result + ((pi == null) ? 0 : pi.hashCode());
            result = prime * result + ((rhs == null) ? 0 : rhs.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            RewriteStep other = (RewriteStep) obj;
            if (lhs == null) {
                if (other.lhs != null)
                    return false;
            } else if (!lhs.equals(other.lhs))
                return false;
            if (pi == null) {
                if (other.pi != null)
                    return false;
            } else if (!pi.equals(other.pi))
                return false;
            if (rhs == null) {
                if (other.rhs != null)
                    return false;
            } else if (!rhs.equals(other.rhs))
                return false;
            return true;
        }

        @Override
        public String toString() {
            return lhs == null ? rhs.toString() : (lhs + " -> " + rhs);
        }

        public Pair<RewriteStep, Integer> renumberVariables(Map<TRSVariable, TRSVariable> map, String prefix, int count) {
            ImmutablePair<? extends TRSFunctionApplication, Integer> pr = rhs.renumberVariables(map, prefix, count);
            ImmutablePair<? extends TRSFunctionApplication, Integer> pl = lhs == null ? null : lhs.renumberVariables(map, prefix, pr.y);
            return new Pair<>(new RewriteStep(pi, pl == null ? null : pl.x, pr.x), pr.y);
        }

    }

    /*
     * The variable names are normalized in all rewrite sequences.
     * In this way, rewrite sequences which are equal up to variable renaming are processed only once.
     */
    public static class RewriteSeq implements Exportable {

        List<RewriteStep> steps;
        TRSFunctionApplication startTerm;

        RewriteSeq(TRSFunctionApplication startTerm, List<RewriteStep> steps) {
            Map<TRSVariable, TRSVariable> map = new LinkedHashMap<>();
            ImmutablePair<? extends TRSFunctionApplication, Integer> p = startTerm.renumberVariables(map, "x", 0);
            this.startTerm = p.x;
            int count = p.y;
            List<RewriteStep> normalizedSteps = new ArrayList<>(steps.size());
            for (RewriteStep step: steps) {
                Pair<RewriteStep, Integer> pair = step.renumberVariables(map, "x", count);
                normalizedSteps.add(pair.x);
                count = pair.y;
            }
            this.steps = normalizedSteps;
        }

        RewriteSeq append(RewriteStep step, TRSSubstitution sigma) {
            List<RewriteStep> newSteps = new ArrayList<>();
            for (RewriteStep s: steps) {
                newSteps.add(new RewriteStep(s.pi, s.lhs == null ? null : s.lhs.applySubstitution(sigma), s.rhs.applySubstitution(sigma)));
            }
            newSteps.add(step);
            return new RewriteSeq(startTerm.applySubstitution(sigma), newSteps);
        }

        boolean isInnermost(Set<Rule> rules) {
            for (RewriteStep step: steps) {
                if (!step.isInnermost(rules)) {
                    return false;
                }
            }
            return true;
        }

        boolean isBasic(Set<FunctionSymbol> definedSymbols) {
            if (!definedSymbols.contains(startTerm.getRootSymbol())) {
                return false;
            }
            for (TRSTerm arg: startTerm.getArguments()) {
                if (!Collection_Util.areDisjoint(arg.getFunctionSymbols(), definedSymbols)) {
                    return false;
                }
            }
            return true;
        }

        TRSFunctionApplication getRes() {
            return steps.isEmpty() ? startTerm : steps.get(steps.size() - 1).rhs;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((startTerm == null) ? 0 : startTerm.hashCode());
            result = prime * result + ((steps == null) ? 0 : steps.hashCode());
            return result;
        }

        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            RewriteSeq other = (RewriteSeq) obj;
            if (startTerm == null) {
                if (other.startTerm != null)
                    return false;
            } else if (!startTerm.equals(other.startTerm))
                return false;
            if (steps == null) {
                if (other.steps != null)
                    return false;
            } else if (!steps.equals(other.steps))
                return false;
            return true;
        }

        @Override
        public String toString() {
            return startTerm + " ->* " + getRes();
        }

        RewriteSeq dropInit() {
            return new RewriteSeq(startTerm, steps.subList(steps.size() - 1, steps.size()));
        }

        /**
         * drop all information but the rhs from each step of this rewrite sequences
         * the other information is just needed for innermost rewriting
         */
        RewriteSeq justRhs() {
            return new RewriteSeq(startTerm, steps.stream().map(x -> new RewriteStep(null, null, x.rhs)).collect(toList()));
        }

        @Override
        public String export(Export_Util eu) {
            return startTerm.export(eu) + eu.appSpace() + eu.rightarrow() + eu.sup("*") + eu.appSpace() + getRes().export(eu);
        }

    }

    public static Set<RewriteSeq> narrow(RuntimeComplexityRelTrsProblem cpxTrs,
            Abortion aborter,
            boolean innermost,
            Set<RewriteSeq> todoArg,
            Set<FunctionSymbol> definedSymbols) {
        // we already know that these rewrite sequences don't correspond to prefixes of infinite narrowing sequences
        Set<RewriteSeq> done = new LinkedHashSet<>();
        // rewrite sequences where the result is a narrowing-normal-form
        Set<RewriteSeq> terminated = new LinkedHashSet<>();
        // if the boolean flag is true, then we are currently constructing the narrowing tree for the rhs of the
        // corresponding rewrite sequence
        Stack<Pair<RewriteSeq, Boolean>> todo = new Stack<>();
        for (RewriteSeq seq: todoArg) {
            todo.add(new Pair<>(seq, false));
        }
        CollectionMap<FunctionSymbol, Rule> rules = new CollectionMap<>();
        for (Rule r: cpxTrs.getRules()) {
            rules.add(r.getRootSymbol(), r);
        }
        while (!todo.isEmpty()) {
            Pair<RewriteSeq, Boolean> pair = todo.pop();
            RewriteSeq seq = pair.x;
            boolean processed = pair.y;
            // if we pop a rewrite sequence whose narrowing tree is currently being constructed, then this means that
            // we finished constructing its narrowing tree
            if (processed || done.contains(seq)) {
                done.add(seq);
                continue;
            } else {
                // otherwise, remember that we now start to construct the narrowing tree for this rewrite sequence
                pair.y = true;
                todo.push(pair);
            }
            TRSFunctionApplication t = seq.getRes();
            boolean normalForm = true;
            for (Pair<Position, TRSTerm> p: t.getPositionsWithSubTerms()) {
                Position pi = p.x;
                TRSTerm s = p.y;
                if (s.isVariable())  {
                    continue;
                }
                for (Rule rr: rules.getNotNull(((TRSFunctionApplication) s).getRootSymbol())) {
                    aborter.checkAbortion();
                    Rule r = rr.renameVariables(t.getVariables());
                    TRSSubstitution mgu = r.getLeft().getMGU(s);
                    if (mgu != null) {
                        TRSFunctionApplication left = t.applySubstitution(mgu);
                        TRSTerm right = t.replaceAt(pi, r.getRight()).applySubstitution(mgu);
                        if (!right.isVariable()) {
                            RewriteStep step = new RewriteStep(pi, left, (TRSFunctionApplication) right);
                            RewriteSeq newSeq = seq.append(step, mgu);
                            if (newSeq.isBasic(definedSymbols)) {
                                if (innermost) {
                                    if (newSeq.isInnermost(cpxTrs.getRules())) {
                                        normalForm = false;
                                        todo.push(new Pair<>(newSeq, false));
                                    }
                                } else {
                                    normalForm = false;
                                    todo.push(new Pair<>(newSeq.dropInit().justRhs(), false));
                                }
                            }
                        }
                    }
                }
            }
            if (normalForm) {
                terminated.add(seq);
            }
        }
        return terminated;
    }

    class NarrowingOnBasicTermsTerminatesProof extends DefaultProof {

        private Set<RewriteSeq> seqs;

        public NarrowingOnBasicTermsTerminatesProof(Set<RewriteSeq> seqs) {
            this.seqs = seqs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("Constant runtime complexity proven by termination of constructor-based narrowing.");
            sb.append(o.paragraph());
            sb.append("The maximal most general narrowing sequences give rise to the following rewrite sequences:");
            sb.append(o.paragraph());
            for (RewriteSeq seq: seqs) {
                sb.append(seq.export(o));
                sb.append(o.newline());
            }
            sb.append(o.newline());
            return sb.toString();
        }

    }

}
