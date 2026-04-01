package aprove.verification.complexity.LowerBounds.BasicStructures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Complexity.*;
import aprove.verification.complexity.LowerBounds.ComplexityComputation.*;
import aprove.verification.complexity.LowerBounds.EquationalRewriting.Structures.*;

public interface InductionProof {

    boolean successful();
    boolean wasCanceled();

    public static InductionProof UNSUCCSESSFUL = new InductionProof() {

        @Override
        public boolean successful() {
            return false;
        }

        @Override
        public boolean wasCanceled() {
            return false;
        }

        @Override
        public String toString() {
            return "unsuccessful induction proof";
        }

    };

    public static InductionProof CANCELED = new InductionProof() {

        @Override
        public boolean successful() {
            return false;
        }

        @Override
        public boolean wasCanceled() {
            return true;
        }

        @Override
        public String toString() {
            return "canceled induction proof";
        }

    };

    public static class SuccessfulInductionProof implements InductionProof, Exportable {

        private RewriteSequence proofOfInductionBase;
        private RewriteSequence proofOfInductionStep;

        public SuccessfulInductionProof(InductionBase ib, InductionStep is) {
            super();
            this.proofOfInductionBase = ib.getProof();
            this.proofOfInductionStep = is.getProof();
        }

        public Complexity getComplexity(LowerBoundsToolbox toolbox) {
            Complexity res = new RewriteSeqToComplexity(this.proofOfInductionStep, toolbox).execute();
            if (res.isPolynomial()) {
                Complexity ibComplexity = new RewriteSeqToComplexity(this.proofOfInductionBase, toolbox).execute();
                if (ibComplexity.isPolynomial()) {
                    res = ((PolynomialComplexity) res).plus((PolynomialComplexity) ibComplexity).setCoefficientsToOne();
                } else if (ibComplexity.compareTo(res) > 0) {
                    res = ibComplexity;
                }
            }
            return res;
        }

        @Override
        public boolean successful() {
            return true;
        }

        @Override
        public boolean wasCanceled() {
            return false;
        }

        @Override
        public String export(Export_Util eu) {
            String res = eu.escape("Induction Base:");
            res += eu.linebreak();
            res += this.proofOfInductionBase.export(eu);
            res += eu.paragraph();
            res += eu.escape("Induction Step:");
            res += eu.linebreak();
            res += this.proofOfInductionStep.export(eu);
            return res;
        }

        public boolean isTrivial() {
            Set<AbstractRule> appliedRules = proofOfInductionStep.getRules();
            return appliedRules.size() < 2 || !appliedRules.stream().anyMatch(x -> x instanceof InductionHypothesis);
        }

    }

    static abstract class PartialInductionProof {

        private RewriteSequence proof;

        public PartialInductionProof(RewriteSequence proof) {
            super();
            this.proof = proof;
        }

        public RewriteSequence getProof() {
            return this.proof;
        }

    }

    public static class InductionBase extends PartialInductionProof {

        public InductionBase(RewriteSequence proof) {
            super(proof);
        }

    }

    public static class InductionStep extends PartialInductionProof {

        public InductionStep(RewriteSequence proof) {
            super(proof);
        }

    }

}