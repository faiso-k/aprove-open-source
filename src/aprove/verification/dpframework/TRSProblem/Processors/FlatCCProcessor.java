package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.NameGenerators.*;
import aprove.xml.*;
import immutables.*;

/**
 * Flat Context Closure for TRSs
 *
 * @author CKuknat
 */

public class FlatCCProcessor extends QTRSProcessor {

    @Override
    public boolean isQTRSApplicable(final QTRSProblem o) {
        return !o.getR().isEmpty();
    }

    @Override
    public Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti)
        throws AbortionException
    {
        final Set<Rule> rules = qtrs.getR();

        // If Q is empty, flat cc is complete,
        // otherwise we can only guarantee soundness!
        final boolean qIsEmpty = qtrs.getQ().isEmpty();

        boolean isApplicable = true;

        // flat-CC is not applicable on a constant-only system
        final Set<FunctionSymbol> signature = qtrs.getRSignature();
        boolean constantOnly = true;
        for (final FunctionSymbol sym : signature) {
            if (sym.getArity() > 0) {
                constantOnly = false;
                break;
            }
        }
        if (constantOnly) {
            isApplicable = false;
        }

        // Apply flat-cc, if applicable
        if (isApplicable) {

            final LinkedHashSet<Context> flatContexts = new LinkedHashSet<Context>();

            // Make every rule in R root-preserving
            // i.e. create new rules for every non root-preserving rule

            // first we need fresh names for the variables in the flat contexts
            @SuppressWarnings("unchecked")
            final Set<TRSVariable> varNames =
                (Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(rules);
            final NameGenerator ng = new AppendNameGenerator(0, 0);
            final FreshNameGenerator fng = new FreshNameGenerator(varNames, ng);
            final Set<Rule> newRules = RootLabelingUtility.flatContext(rules, null, aborter, flatContexts, fng);
            if (rules.equals(newRules)) {
                return ResultFactory.unsuccessful("This QTRS is already root-preserving.");
            }

            // Create a new QTRS problem with empty Q
            final QTRSProblem newQTRS = QTRSProblem.create(ImmutableCreator.create(newRules));

            final Proof proof = new FlatCCProof(qIsEmpty, qtrs, newQTRS, flatContexts);

            return ResultFactory.proved(newQTRS, (qIsEmpty ? YNMImplication.EQUIVALENT : YNMImplication.SOUND), proof);
        }
        return ResultFactory.notApplicable("flat context closure is not applicable here");
    }

    /**
     * Proof which prints out the flat context closure operations
     */
    private static class FlatCCProof extends QTRSProof {

        private final boolean qIsEmpty;
        private final QTRSProblem origObl;
        private final QTRSProblem resultObl;
        private final Collection<Context> flatContexts;

        private FlatCCProof(
            final boolean qIsEmpty,
            final QTRSProblem origObl,
            final QTRSProblem resultObl,
            final Collection<Context> flatContexts)
        {
            this.qIsEmpty = qIsEmpty;
            this.origObl = origObl;
            this.resultObl = resultObl;
            this.flatContexts = flatContexts;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append("We used flat context closure " + eu.cite(Citation.ROOTLAB) + "\n");
            if (this.qIsEmpty) {
                s.append("As Q is empty the flat context closure was sound AND complete.\n");
            }
            return s.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {

            if (modus.isPositive()) {
                final Element flatContextsTag = CPFTag.FLAT_CONTEXTS.create(doc);
                for (final Context context : this.flatContexts) {
                    flatContextsTag.appendChild(context.toCPF(doc, xmlMetaData));
                }
                return CPFTag.TRS_TERMINATION_PROOF.create(
                    doc,
                    CPFTag.FLAT_CONTEXT_CLOSURE.create(
                        doc,
                        flatContextsTag,
                        CPFTag.trs(doc, xmlMetaData, this.resultObl.getR()),
                        childrenProofs[0]));
            } else {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }

    }
}
