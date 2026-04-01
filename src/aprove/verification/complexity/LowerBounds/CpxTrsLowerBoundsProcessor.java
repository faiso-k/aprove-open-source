package aprove.verification.complexity.LowerBounds;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Obligations.Junctors.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.InductionProof.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class CpxTrsLowerBoundsProcessor extends Processor.ProcessorSkeleton {

    @SuppressWarnings("serial")
    public static class ExponentialLowerBoundException extends Exception {
    }

    public static class Options {
        public boolean indefinite = false;
    }

    private final Options options;

    @ParamsViaArgumentObject
    public CpxTrsLowerBoundsProcessor(Options options) {
        this.options = options;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        TruthValue truth = obl.getTruthValue();
        if (truth instanceof ComplexityYNM) {
            ComplexityYNM complexity = (ComplexityYNM) truth;
            if (complexity.getLowerBound().isInfinite()) {
                return false;
            }
        }
        return obl instanceof OrderedCpxTrsLowerBoundsProblem && aprove.runtime.Options.certifier == Certifier.NONE;
    }

    @Override
    public Result
            process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        CpxTrsLowerBoundsWorker worker = new CpxTrsLowerBoundsWorker();
        return worker.process(obl, oblNode, aborter, rti);
    }

    private class CpxTrsLowerBoundsWorker {

        OrderedCpxTrsLowerBoundsProblem cpxObl;
        Conjecture conjecture;
        SuccessfulInductionProof successfulProof;
        Lemma lemma;
        LowerBoundsToolbox toolbox;

        @SuppressWarnings("unused")
        public Result
                process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
            this.cpxObl = (OrderedCpxTrsLowerBoundsProblem) obl;
            Optional<Result> res;
            do {
                if (this.cpxObl.isEmpty()) {
                    return ResultFactory.unsuccessful();
                }
                this.toolbox = new LowerBoundsToolbox(this.cpxObl, aborter);
                this.searchLemmas(CpxTrsLowerBoundsProcessor.this.options.indefinite);
                res = this.result();
                if (res.isPresent()) {
                    return res.get();
                } else {
                    cpxObl = next();
                }
            } while (true);
        }

        void searchLemmas(boolean indefinite) {
            LemmaGenerator lemgen = new LemmaGenerator(this.toolbox, this.toolbox.aborter.createChild(20000));
            try {
                lemgen.generate(indefinite);
            } catch (AbortionException e) {
                // do nothing
            }
            Pair<Conjecture, Set<InductionProof>> p = lemgen.result();
            if (p != null) {
                this.conjecture = p.x;
                for (InductionProof proof : p.y) {
                    SuccessfulInductionProof aProof = (SuccessfulInductionProof) proof;
                    if (!aProof.isTrivial()) {
                        Complexity complexity = aProof.getComplexity(this.toolbox);
                        Lemma newLemma = this.conjecture.toLemma(complexity);
                        if (complexity.isExponential() && newLemma.getDegreeOfStartTermSize(toolbox.types) > 1) {
                            // This is a really strange case where the complexity induced by the lemma is unclear.
                            // If e is the degree of the size of the start term, then we get something strange like 2^Omega(e-th root of n).
                            // If this is exponential or not is debatable, so lets better ignore such lemmas.
                            // Fortunately, this does not happen in practice.
                            continue;
                        }
                        if (this.lemma == null || this.lemma.getComplexity().compareTo(complexity) < 0) {
                            this.lemma = newLemma;
                            this.successfulProof = aProof;
                        }
                    }
                }
                if (this.lemma != null) {
                    this.lemma.addToTrs(this.toolbox.trs);
                }
            }
        }

        private Optional<Result> result() {
            if (this.lemma != null) {
                if (this.lemma.getComplexity().isExponential()) {
                    return Optional.of(ResultFactory.provedWithValue(ComplexityYNM.createLower(this.toolbox.trs.getComplexity()), this.getProof()));
                }
                List<BasicObligation> todo = new ArrayList<>();
                // continue with the next symbol to analyze
                OrderedCpxTrsLowerBoundsProblem next = this.next();
                ComplexityValue currentLower = cpxObl.getRes();
                ComplexityValue newLower = next.getTrs().getComplexity();
                // if this lemma improves the current result add a branch to the proof tree that
                // terminates immediately to make sure that the improved result is propagated
                if (newLower.compareTo(currentLower) > 0) {
                    todo.add(new ProvenLowerBound(cpxObl, newLower));
                }
                if (!next.isEmpty()) {
                    todo.add(next);
                }
                return Optional.of(ResultFactory.provedWithJunctor(todo, Junctors.BEST, LowerBound.create(), this.getProof()));
            } else {
                return Optional.empty();
            }
        }

        private OrderedCpxTrsLowerBoundsProblem next() {
            return this.cpxObl.next(this.toolbox.trs);
        }

        private Proof getProof() {
            return new RewriteLemmaProof(this.lemma, this.successfulProof, this.conjecture.getDegreeOfStartTermSize(this.toolbox.types));
        }

    }

    static class RewriteLemmaProof extends DefaultProof {

        private Lemma lemma;
        private SuccessfulInductionProof inductionProof;
        private int szDegree;

        public RewriteLemmaProof(Lemma lemma, SuccessfulInductionProof inductionProof, int degreeOfStartTermSize) {
            super();
            this.lemma = lemma;
            this.inductionProof = inductionProof;
            this.szDegree = degreeOfStartTermSize;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            ComplexityValue complexityClass = this.lemma.getComplexity().asymptotic();
            boolean polynomial = false;
            int rtDegree = 0;
            if (complexityClass instanceof FixedDegreePoly) {
                polynomial = true;
                rtDegree = ((FixedDegreePoly) complexityClass).getDegree();
            } else if (complexityClass.isConstant()) {
                polynomial = true;
                rtDegree = 0;
            }
            String res = o.escape("Proved the following rewrite lemma:");
            res += o.linebreak();
            res += this.lemma.export(o);
            res += o.paragraph();
            res += this.inductionProof.export(o);
            res += o.paragraph();
            res += o.escape("We have rt");
            res += o.appSpace();
            res += o.isElement();
            res += o.appSpace();
            res += complexityClass.export(o, o.Omega());
            res += o.appSpace();
            res += o.escape("and sz");
            res += o.appSpace();
            res += o.isElement();
            res += o.appSpace();
            res += o.escape("O(");
            res += o.escape("n");
            if (this.szDegree != 1) {
                res += o.sup(o.escape(Integer.toString(this.szDegree)));
            }
            res += o.escape(")");
            res += o.escape(". Thus, we have irc");
            res += o.sub("R");
            res += o.appSpace();
            res += o.isElement();
            res += o.appSpace();
            if (polynomial) {
                res += o.Omega();
                res += o.escape("(");
                res += o.escape("n");
                int ircDegree = rtDegree / this.szDegree;
                if (ircDegree != 1) {
                    res += o.sup(o.escape(Integer.toString(ircDegree)));
                }
                res += o.escape(").");
            } else {
                res += complexityClass.export(o, o.Omega());
            }
            return res;
        }

    }

}
