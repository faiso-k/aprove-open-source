package aprove.verification.oldframework.WeightedIntTrs;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

public abstract class WeightedIntTrsToKoATLikeBackendProcessor<T extends CpxIntTrsToKoATLikeBackendProcessor.Arguments, S extends CpxIntTrsToKoATLikeBackendProcessor<T>> extends Processor.ProcessorSkeleton {

    private S cpxIntTrsProcessor;

    protected WeightedIntTrsToKoATLikeBackendProcessor(S proc) {
        this.cpxIntTrsProcessor = proc;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        WeightedIntTrs its = (WeightedIntTrs) obl;
        if (its.isEmpty()) {
            return ResultFactory.provedWithValue(ComplexityYNM.CONSTANT, new EmptyWeightedIntTrsProof());
        }
        String export = toKoAT(its);
        List<String> proof = cpxIntTrsProcessor.obtainProof(export, aborter);
        if (proof == null) {
            return onKoatFail(its, new KoatException("Koat execution unsuccessfull", null));
        }
        String result = cpxIntTrsProcessor.obtainResult(proof);
        if (result == null) {
            return onKoatFail(its, new KoatException("Koat could not prove a complexity bound", proof));
        }
        return onKoatSucces(its, result, proof);
    }

    public static String toKoAT(WeightedIntTrs its) {
        String newline = System.lineSeparator();
        FunctionSymbol startSymbol = its.getStartTerm().getRootSymbol();
        StringBuilder sb = new StringBuilder();
        sb.append("(GOAL COMPLEXITY)" + newline);
        sb.append("(STARTTERM (FUNCTIONSYMBOLS ");
        sb.append(startSymbol.getName());
        sb.append("))" + newline);
        sb.append("(VAR");
        for (TRSVariable x: its.getVariables()) {
            sb.append(" " + x);
        }
        sb.append(")" + newline);
        sb.append("(RULES" + newline);
        for (WeightedRule e: its.getRules()) {
            sb.append(e.toString() + newline);
        }
        sb.append(")" + newline);
        return sb.toString();
    }

    protected Result onKoatFail(WeightedIntTrs obl, KoatException e) {
        return ResultFactory.unsuccessful();
    }

    protected Result onKoatSucces(WeightedIntTrs obl, String result, List<String> proof) {
        ComplexityValue compl = KoATParser.parse(result);
        if (compl == null) {
            return ResultFactory.unsuccessful();
        }
        if (compl.isSuperPolynomial()) {
            return cpxIntTrsProcessor.buildResult(compl, proof);
        }
        SimplePolynomial poly = KoATParser.parseAsPolynomial(result);
        MinMaxExpr mPoly = null;
        if (poly != null) {
            mPoly = poly.toMinMaxExpr().absolutize();
            TRSFunctionApplication startTerm = obl.getStartTerm();
            List<String> args = new ArrayList<>(startTerm.getArguments().size());
            for (int i = 0; i < startTerm.getArguments().size(); i++) {
                args.add ("Ar_" + i);
            }
            mPoly = Util.renameVariablesAccordingToStartTerm(obl.getStartTerm(), mPoly, args);
            compl = compl.withConcreteValue(mPoly);
        }
        return cpxIntTrsProcessor.buildResult(compl, proof);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof WeightedIntTrs && cpxIntTrsProcessor.isInstalled();
    }

    private static class EmptyWeightedIntTrsProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.escape("The IntTRS is empty.");
        }

    }

    public static class KoatException extends Exception {
        /**
         *
         */
        private static final long serialVersionUID = -399707366878151391L;
        private List<String> koatProof;

        public KoatException(String reason, List<String> koatProof) {
            super(reason);
            this.koatProof = koatProof;
        }

        public List<String> getKoatProof() {
            return koatProof;
        }
    }

}
