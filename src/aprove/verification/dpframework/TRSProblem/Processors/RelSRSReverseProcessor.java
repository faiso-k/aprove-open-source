package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Relative SRS Reverse processor. Reverses any relative TRS problem
 * whose signature only contains 0-ary or 1-ary function symbols.
 * The reversed terms will contain new function symbols instead
 * of the 0-ary symbols, and they will all be terminated by one
 * and the same (possibly) new variable regardless of whether a
 * variable or a constant was the leaf of the original term.
 *
 * @author Carsten Fuhs, Ulrich Schmidt-Goertz
 * @version $Id$
 */
@NoParams
public class RelSRSReverseProcessor extends RelTRSProcessor {

    /**
     * This is a string rewriting processor. In CoLoR mode, it can only be used when the input file
     * is in SRS format, so we must check this. The "isSRS" metadata is set in CLI.Main or by
     * the GUI's GoAction depending on the input file's extension. Crude, but that's how it works.
     * Update: At least for CPF export, this restriction shouldn't be applicable any more.
     */
    @Override
    public Result process(final BasicObligation o, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {

        if (!Options.certifier.isCpf() && Options.certifier.isRainbow() && (rti.getMetadata(Metadata.IS_SRS) != Boolean.TRUE)) {
            return ResultFactory.notApplicable("In CoLoR mode, Reverse is applicable to SRS *files* only.");
        }
        final RelTRSProblem problem = (RelTRSProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(QTRSProcessor.rIsEmptyProof);
        } else {
            return this.processRelTRS(problem, aborter, rti);
        }
    }

    @Override
    public Result processRelTRS(final RelTRSProblem problem, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {
        final ImmutableSet<Rule> r = problem.getR();
        final ImmutableSet<Rule> s = problem.getS();
        final Set<Rule> newR = new LinkedHashSet<>(r.size());
        final Set<Rule> newS = new LinkedHashSet<>(s.size());

        // the symbols that exist so far and that hence must not be used for
        // fresh ones (actually, only those of arity 1 matter)
        Set<FunctionSymbol> allSyms;
        allSyms = new HashSet<>(problem.getSignature());

        // the mapping of constants to the new symbols that are used to
        // take their place in the reversed term
        Map<FunctionSymbol, FunctionSymbol> newSyms;
        newSyms = new HashMap<>();

        for (final Rule rule : r) {
            newR.add(ReverseProcessor.reverse(rule, allSyms, newSyms));
            aborter.checkAbortion();
        }

        for (final Rule rule : s) {
            newS.add(ReverseProcessor.reverse(rule, allSyms, newSyms));
            aborter.checkAbortion();
        }

        final RelTRSProblem newProblem = RelTRSProblem.create(ImmutableCreator.create(newR),
                ImmutableCreator.create(newS));
        final Proof proof = new RelTRSReverseProof(problem, newProblem, newSyms);
        final Result result =
            ResultFactory.proved(
                newProblem,
                newSyms.isEmpty() ? YNMImplication.EQUIVALENT : YNMImplication.SOUND,
                proof);
        return result;
    }

    @Override
    public boolean isRelTRSApplicable(final RelTRSProblem problem) {
        if (Options.certifier.isA3pat() || Options.certifier.isCeta() || Options.certifier.isRainbow()) {
            Set<FunctionSymbol> fs = problem.getSignature();
            return RelSRSReverseProcessor.onlyArityOne(fs);
        } else {
            return problem.isSRS();
        }
    }

    /**
     * @param fs - non-null, no null elements
     * @return whether all symbols in fs have arity one
     */
    private static boolean onlyArityOne(Collection<FunctionSymbol> fs) {
        for (FunctionSymbol f : fs) {
            int n = f.getArity();
            if (n != 1) {
                return false;
            }
        }
        return true;
    }

    private static class RelTRSReverseProof extends RelTRSProof {

        private final RelTRSProblem before;
        private final RelTRSProblem after;
        private final Map<FunctionSymbol, FunctionSymbol> constantMap;

        private RelTRSReverseProof(
            final RelTRSProblem before,
            final RelTRSProblem after,
            final Map<FunctionSymbol, FunctionSymbol> constantMap)
        {
            this.shortName = "RelTRS Reverse";
            this.longName = this.shortName;
            this.before = before;
            this.after = after;
            this.constantMap = constantMap;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder(64);
            res.append("We have reversed the following relative TRS "+ o.cite(Citation.REVERSE)+":");
            res.append(o.cond_linebreak());
            res.append("The set of rules R is ");
            res.append(o.set(this.before.getR(), Export_Util.RULES));
            res.append(o.cond_linebreak());
            res.append("The set of rules S is ");
            res.append(o.set(this.before.getS(), Export_Util.RULES));
            res.append(o.cond_linebreak());
            res.append("We have obtained the following relative TRS:");
            res.append(o.cond_linebreak());
            res.append("The set of rules R is ");
            res.append(o.set(this.after.getR(), Export_Util.RULES));
            res.append(o.cond_linebreak());
            res.append("The set of rules S is ");
            res.append(o.set(this.after.getS(), Export_Util.RULES));
            res.append(o.cond_linebreak());
            return res.toString();
        }

        @Override
        public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
            final Element reverseTag = XMLTag.RELTRS_REVERSE_PROOF.createElement(doc);

            final Element reverseTRS = XMLTag.TRS.createElement(doc);
            for (final Rule rule : this.after.getR()) {
                reverseTRS.appendChild(rule.toDOM(doc, xmlMetaData));
            }
            reverseTag.appendChild(reverseTRS);

            return reverseTag;
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            return (modus.isPositive() ? CPFTag.RELATIVE_TERMINATION_PROOF : CPFTag.RELATIVE_NONTERMINATION_PROOF).create(doc,
                    CPFTag.STRING_REVERSAL.create(doc,
                            CPFTag.trs(doc, xmlMetaData, this.after.getR()),
                            CPFTag.trs(doc, xmlMetaData, this.after.getS()),
                            childrenProofs[0]));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return this.constantMap.isEmpty();
        }

        @Override
        public String getNonCPFExportableReason(final CPFModus modus) {
            return "String reversal for relative termination with constants";
        }

    }
}
