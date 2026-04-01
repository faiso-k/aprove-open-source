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
 * Flat Context Closure for relative TRSs (adaptation from FlatCCProcessor)
 *
 * @author CKuknat (adapted by R. Thiemann)
 */

public class RelFlatCCProcessor extends RelTRSProcessor {

    @Override
    public boolean isRelTRSApplicable(final RelTRSProblem o) {
        return !(o.getR().isEmpty() && o.getS().isEmpty());
    }

    @SuppressWarnings("unchecked")
    @Override
    public Result processRelTRS(RelTRSProblem rtrs, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        final Set<Rule> r = rtrs.getR();
        final Set<Rule> s = rtrs.getS();
        // flat-CC is not applicable on a constant-only system
        final Set<FunctionSymbol> signature = rtrs.getSignature();
        // Apply flat-cc, if applicable
        if (!FunctionSymbol.onlyConstants(signature)) {
            final LinkedHashSet<Context> flatContexts = new LinkedHashSet<>();
            // Make every rule in R and S root-preserving
            // i.e. create new rules for every non root-preserving rule
            // first we need fresh names for the variables in the flat contexts
            Set<Rule> newR = new LinkedHashSet<>(r.size());
            Set<Rule> newS = new LinkedHashSet<>(s.size());
            // Make every rule in R and S root-preserving
            // i.e. create new rules for every non root-preserving rule
            // first we need fresh names for the variables in the flat contexts
            final Set<TRSVariable> varNames =
                (Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(r);
            varNames.addAll((Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(s));
            final NameGenerator ng = new AppendNameGenerator(0, 0);
            final FreshNameGenerator fng = new FreshNameGenerator(varNames, ng);
            newR = RootLabelingUtility.flatContext(r, signature, aborter, flatContexts, fng);
            newS = RootLabelingUtility.flatContext(s, signature, aborter, flatContexts, fng);
            if (r.equals(newR) && s.equals(newS)) {
                return ResultFactory.unsuccessful("This relative TRS is already root-preserving.");
            }
            // Create a new relative TRS problem
            final RelTRSProblem newRelTRS =
                RelTRSProblem.create(ImmutableCreator.create(newR), ImmutableCreator.create(newS));
            final Proof proof = new FlatCCProof(rtrs, newRelTRS, flatContexts);
            return ResultFactory.proved(newRelTRS, YNMImplication.EQUIVALENT, proof);
        }
        return ResultFactory.notApplicable("flat context closure is not applicable here");
    }

    /**
     * Proof which prints out the flat context closure operations
     */
    private static class FlatCCProof extends RelTRSProof {

        private final RelTRSProblem origObl;
        private final RelTRSProblem resultObl;
        private final Collection<Context> flatContexts;

        private FlatCCProof(
            final RelTRSProblem origObl,
            final RelTRSProblem resultObl,
            final Collection<Context> flatContexts)
        {
            this.origObl = origObl;
            this.resultObl = resultObl;
            this.flatContexts = flatContexts;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append("We used flat context closure " + eu.cite(Citation.ROOTLAB) + "\n");
            return s.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            if (modus.isPositive()) {
                final Element flatContextsTag = CPFTag.FLAT_CONTEXTS.create(doc);
                for (final Context context : this.flatContexts) {
                    flatContextsTag.appendChild(context.toCPF(doc, xmlMetaData));
                }
                return CPFTag.RELATIVE_TERMINATION_PROOF.create(
                    doc,
                    CPFTag.FLAT_CONTEXT_CLOSURE.create(
                        doc,
                        flatContextsTag,
                        CPFTag.trs(doc, xmlMetaData, this.resultObl.getR()),
                        CPFTag.trs(doc, xmlMetaData, this.resultObl.getS()),
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
