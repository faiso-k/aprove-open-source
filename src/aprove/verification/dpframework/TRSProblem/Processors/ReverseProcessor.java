package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * QTRS Reverse processor. Reverses any QTRS problem whose
 * signature only contains 0-ary or 1-ary function symbols.
 * The reversed terms will contain new function symbols instead
 * of the 0-ary symbols, and they will all be terminated by one
 * and the same (possibly) new variable regardless of whether a
 * variable or a constant was the leaf of the original term.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
@NoParams
public class ReverseProcessor extends QTRSProcessor {

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
        final QTRSProblem problem = (QTRSProblem) o; // this cast will succeed (see isApplicable)
        if (problem.getR().isEmpty()) {
            return ResultFactory.proved(QTRSProcessor.rIsEmptyProof);
        } else {
            return this.processQTRS(problem, aborter, rti);
        }
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti)
            throws AbortionException {

        Pair<Set<Rule>, Map<FunctionSymbol,FunctionSymbol>> res
            = ReverseProcessor.reverse(qtrs);

        // just throw away Q
        final QTRSProblem newProblem = QTRSProblem.create(ImmutableCreator.create(res.x));
        final Proof proof = new ReverseProof(qtrs, newProblem, res.y);
        final YNMImplication impl = ReverseProcessor.computeImplication(qtrs, aborter);
        final Result result = ResultFactory.proved(newProblem, impl, proof);
        return result;
    }

    private static Pair<Set<Rule>, Map<FunctionSymbol,FunctionSymbol>> reverse(QTRSProblem qtrs) {
        final ImmutableSet<Rule> r = qtrs.getR();
        final Set<Rule> newR = new LinkedHashSet<>(r.size());

        // the symbols that exist so far and that hence must not be used for
        // fresh ones (actually, only those of arity 1 matter)
        Set<FunctionSymbol> allSyms;
        allSyms = new HashSet<>(qtrs.getSignature());

        // the mapping of constants to the new symbols that are used to
        // take their place in the reversed term
        Map<FunctionSymbol, FunctionSymbol> newSyms;
        newSyms = new HashMap<FunctionSymbol, FunctionSymbol>();

        for (final Rule rule : r) {
            newR.add(ReverseProcessor.reverse(rule, allSyms, newSyms));
        }

        return new Pair<>(newR, newSyms);
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return (qtrs.getMaxArity() <= 1);
    }

    /**
     * Examples: (only x and y are variables here)
     * (fgfgx, y, {}) --> gfgfy
     * (fgfgx, x, {}) --> gfgfx
     * (fga, y, {b'}) --> a'gfy
     * (fga, y, {a'}) --> a''gfy
     *
     * @param reversee to be reversed, may only contain 0ary and 1ary symbols
     * @param x the variable to occur as leaf of the result
     * @param allSyms none of the symbols in there will be used as fresh
     *  FunctionSymbols; if a new one is introduced in the process, it
     *  will be stored here
     * @param newSyms maps the constants to the newly introduced function
     *  symbols
     * @return the reversed term, introducing a new FunctionSymbol as root
     *  if the leaf of reversee is a constant
     */
    static TRSTerm reverse(TRSTerm reversee, final TRSVariable x,
            final Set<FunctionSymbol> allSyms, final Map<FunctionSymbol, FunctionSymbol> newSyms) {
        TRSTerm t = x;
        while (! reversee.isVariable()) {
            final TRSFunctionApplication fapp = (TRSFunctionApplication) reversee;
            final FunctionSymbol rootSym = fapp.getRootSymbol();
            if (rootSym.getArity() == 1) {
                t = TRSTerm.createFunctionApplication(rootSym, new TRSTerm[] {t});
            }
            else {
                if (Globals.useAssertions) {
                    assert rootSym.getArity() == 0;
                }
                FunctionSymbol newRootSym = newSyms.get(rootSym);
                if (newRootSym == null) {
                    // we see the constant symbol rootSym for the first time
                    newRootSym = rootSym;
                    boolean reallyAdded;
                    do {
                        newRootSym = FunctionSymbol.create(newRootSym.getName() + "'", 1);
                        reallyAdded = allSyms.add(newRootSym);
                        // make sure the new unary function symbol really *is* new
                    } while (! reallyAdded);
                    newSyms.put(rootSym, newRootSym);
                }
                // rootSym occurs at a leaf, so there is no variable that would
                // terminate the term (and the loop)
                return TRSTerm.createFunctionApplication(newRootSym, new TRSTerm[] {t});
            }
            reversee = fapp.getArgument(0);
        }
        return t;
    }

    private static final TRSVariable DEFAULT_VAR = TRSVariable.createVariable("x");

    /**
     * reversing a rule, by applying reverse of a term on both sides
     * @param rule
     * @param allSyms
     * @param newSyms
     * @return
     */
    static Rule reverse(final Rule rule, final Set<FunctionSymbol> allSyms, final Map<FunctionSymbol, FunctionSymbol> newSyms) {
        TRSFunctionApplication newLeft;
        final Iterator<TRSVariable> i = rule.getLeft().getVariables().iterator();
        final TRSVariable var = i.hasNext() ? i.next() : ReverseProcessor.DEFAULT_VAR;
        newLeft = (TRSFunctionApplication) ReverseProcessor.reverse(rule.getLeft(), var,
                allSyms, newSyms);
        // cast works because rule.getLeft() must be a
        // FunctionApplication, too

        final TRSTerm newRight = ReverseProcessor.reverse(rule.getRight(), var, allSyms, newSyms);
        return Rule.create(newLeft, newRight);
    }

    private static YNMImplication computeImplication(final QTRSProblem qtrs,
            final Abortion aborter) throws AbortionException {
        final QTermSet q = qtrs.getQ();
        if (q.isEmpty()) {
            return YNMImplication.EQUIVALENT;
        }
        final CriticalPairs cps = qtrs.getCriticalPairs();
        final QTermSet lhss = new QTermSet(CollectionUtils.getLeftHandSides(qtrs.getR()));
        if (lhss.equals(q) && cps.isOverlay(aborter) &&
                cps.isLocallyConfluent(0, aborter) == YNM.YES) {
            return YNMImplication.EQUIVALENT;
        }
        else {
            return YNMImplication.SOUND;
        }
    }

    private static class ReverseProof extends QTRSProof {

        private final QTRSProblem before;
        private final QTRSProblem after;
        private final Map<FunctionSymbol, FunctionSymbol> constantMap;

        private ReverseProof(final QTRSProblem before, final QTRSProblem after, Map<FunctionSymbol, FunctionSymbol> constantMap) {
            this.shortName = "QTRS Reverse";
            this.longName = this.shortName;
            this.before = before;
            this.after = after;
            this.constantMap = constantMap;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            //StringBuilder res = new StringBuilder(64);
            //res.append("We have reversed the following QTRS"+ o.cite(Citation.REVERSE)+":");
            //res.append(o.cond_linebreak());
            //res.append("The set of rules R is ");
            //res.append(o.set(this.before.getR(), Export_Util.RULES));
            //res.append(o.cond_linebreak());
            //res.append("The set Q is ");
            //if (this.before.getQ().isEmpty()) {
            //    res.append("empty");
            //}
            //else {
            //    res.append(o.set(this.before.getQ().getTerms(),
            //            Export_Util.SIMPLESET));
            //}
            //res.append(".");
            //res.append(o.cond_linebreak());
            //res.append("We have obtained the following QTRS:");
            //res.append(o.set(this.after.getR(), Export_Util.RULES));
            //res.append(o.cond_linebreak());
            //res.append("The set Q is empty.");
            return "We applied the QTRS Reverse Processor "+ o.cite(Citation.REVERSE)+".";
        }

        private Element renaming(final Document doc, final XMLMetaData xmlMetaData) {
            Element e = CPFTag.RENAMING.create(doc);
            for (Map.Entry<FunctionSymbol, FunctionSymbol> me : this.constantMap.entrySet()) {
                e.appendChild(CPFTag.RENAMING_ENTRY.create(doc,
                        me.getKey().toCPF(doc, xmlMetaData),
                        me.getValue().toCPF(doc, xmlMetaData)
                        ));
            }
            return e;
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            CPFTag tag = modus.isPositive() ? CPFTag.TRS_TERMINATION_PROOF : CPFTag.TRS_NONTERMINATION_PROOF;
            Element proof = tag.create(doc,
                    CPFTag.STRING_REVERSAL.create(doc,
                            CPFTag.trs(doc, xmlMetaData, this.after.getR()),
                            childrenProofs[0]));
            if (!this.constantMap.isEmpty()) {
                Set<Rule> intermediateTrs = ReverseProcessor.reverse(this.after).x;
                Element e = CPFTag.CONSTANT_TO_UNARY.create(doc);
                e.appendChild(ReverseProcessor.DEFAULT_VAR.toCPF(doc, xmlMetaData));
                e.appendChild(this.renaming(doc, xmlMetaData));
                e.appendChild(CPFTag.trs(doc, xmlMetaData, intermediateTrs));
                e.appendChild(proof);
                proof = tag.create(doc,e);
            }
            return proof;
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

        @Override
        public String getNonCPFExportableReason(CPFModus modus) {
            return "String reversal with constant in signature of TRS";
        }

    }
}
