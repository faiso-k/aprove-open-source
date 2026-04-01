package aprove.verification.oldframework.IntTRS.TerminationGraph;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Builds the termination graph and returns the SCCs. Furthermore it may merge
 * rules together by applying chaining.
 * @author Matthias Hoelzel
 */
public class IntTRSTerminationGraphProcessor extends Processor.ProcessorSkeleton {
    /** The arguments */
    private final TerminationGraphArguments arguments;

    /** A class for the arguments */
    public static class TerminationGraphArguments {
        /** Use chaining to simplify the SCCs? */
        public boolean useChaining = false;

        /** True iff you only want the default chaining. */
        public boolean defaultChainingOnly = true;

        /** Add further constraints to some rules? */
        public boolean useConstraintTransformation = true;

        /**
         * When this is set to true, then we always returns the obligation, even
         * if the step was unsuccessful. Otherwise we only return the obligation
         * if we have changed the problem.
         */
        public boolean alwaysReturnObligation = false;
    }

    /**
     * A constructor.
     */
    public IntTRSTerminationGraphProcessor() {
        this.arguments = new TerminationGraphArguments();
    }

    /**
     * A constructor.
     * @param args Arguments for this processor.
     */
    public IntTRSTerminationGraphProcessor(final TerminationGraphArguments args) {
        this.arguments = args;
    }

    /**
     * Setter for the argument useChaining.
     * @param val boolean
     */
    public void setUseChaining(final boolean val) {
        this.arguments.useChaining = val;
    }

    /**
     * Setter for the argument defaultChainingOnly.
     * @param val boolean
     */
    public void setDefaultChainingOnly(final boolean val) {
        this.arguments.defaultChainingOnly = val;
    }

    /**
     * Setter for the argument useConstraintTransformation.
     * @param val boolean
     */
    public void setUseConstraintTransformation(final boolean val) {
        this.arguments.useConstraintTransformation = val;
    }

    /**
     * Setter for the argument alwaysReturnObligation
     * @param val boolean
     */
    public void setAlwaysReturnObligation(final boolean val) {
        this.arguments.alwaysReturnObligation = val;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert (obl instanceof IRSwTProblem);
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }
        final IntTRSTerminationGraphProof proof = new IntTRSTerminationGraphProof();

        final IntTRSTerminationGraphWorker worker =
            new IntTRSTerminationGraphWorker(problem, aborter, proof, this.arguments);
        final List<IRSProblem> toSolve = worker.work();
        proof.newProblems = toSolve;

        if (toSolve.isEmpty()) {
            // Nobody wants to see TRUE; everybody wants YES!
            return ResultFactory.proved(proof);
        } else if (!worker.hasChangedProblem() && !this.arguments.alwaysReturnObligation) {
            return ResultFactory.unsuccessful();
        } else {
            return ResultFactory.provedAnd(toSolve, problem.getStartTerm() != null
                ? YNMImplication.SOUND
                    : YNMImplication.EQUIVALENT, proof);
        }
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me), Matthias Hoelzel
     */
    public class IntTRSTerminationGraphProof extends DefaultProof {
        /** Stores information about applied chaining. */
        private final List<Triple<IGeneralizedRule, IGeneralizedRule, IGeneralizedRule>> chainings;

        /** Which rules have been transformed into which rules? */
        private final LinkedList<Pair<IGeneralizedRule, IGeneralizedRule>> bciTransformations;

        /** Number of SCCs. Null if not used. */
        private Integer numberOfSCCs;
        
        private List<IRSProblem> newProblems;

        /** Create the proof. */
        public IntTRSTerminationGraphProof() {
            super();
            this.shortName = "TerminationGraphProcessor";
            this.longName = "IntTRS Termination Graph Processor";

            this.chainings = new LinkedList<>();
            this.numberOfSCCs = null;
            this.bciTransformations = new LinkedList<>();
            this.newProblems = null;
        }

        /**
         * Set the number of SCC obtained
         * @param number integer
         */
        public void setNumberOfSCCs(final Integer number) {
            this.numberOfSCCs = number;
        }

        /**
         * Informs the proof that we have used chaining.
         * @param from the first rule
         * @param to the second rule
         * @param result the result rule
         */
        public
            void
            exportChaining(final IGeneralizedRule from, final IGeneralizedRule to, final IGeneralizedRule result)
        {
            this.chainings.add(new Triple<>(from, to, result));
        }

        /**
         * Which rule has been transformed into which rule?
         * @param from some rule
         * @param to another rule
         */
        public void exportTransformation(final IGeneralizedRule from, final IGeneralizedRule to) {
            this.bciTransformations.add(new Pair<IGeneralizedRule, IGeneralizedRule>(from, to));
        }

        /**
         * @param eu export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder builder = new StringBuilder();
            if (this.numberOfSCCs != null) {
                final String stdText = "Constructed the termination graph and obtained ";
                if (this.numberOfSCCs == 0) {
                    builder.append(eu.indent(eu.bold(eu.tttext(stdText + "no non-trivial SCC(s)."))));
                } else if (this.numberOfSCCs == 1) {
                    builder.append(eu.indent(eu.bold(eu.tttext(stdText + "one non-trivial SCC."))));
                } else {
                    builder.append(eu.indent(eu.bold(eu.tttext(stdText + this.numberOfSCCs + " non-trivial SCCs."))));
                }
            }
            this.exportTransformations(eu, builder);
            this.exportChaining(eu, builder);
            builder.append(eu.linebreak());
            return builder.toString();
        }

        /**
         * Exports some information about the constraint transformation we
         * applied.
         * @param eu export helper
         * @param builder string builder
         */
        private void exportTransformations(final Export_Util eu, final StringBuilder builder) {
            if (this.bciTransformations.size() > 0) {
                builder.append(eu.linebreak());
                for (final Pair<IGeneralizedRule, IGeneralizedRule> p : this.bciTransformations) {
                    builder.append(eu.linebreak());
                    builder.append(p.x.export(eu));
                    builder.append(eu.linebreak());
                    builder.append(eu.tttext("has been transformed into"));
                    builder.append(eu.linebreak());
                    builder.append(p.y.export(eu));
                    builder.append(eu.tttext("."));
                    builder.append(eu.linebreak());
                }
            }
        }

        /**
         * Exports some information about the chaining we did.
         * @param eu export helper
         * @param builder string builder
         */
        private void exportChaining(final Export_Util eu, final StringBuilder builder) {
            if (this.chainings.size() > 0) {
                builder.append(eu.linebreak());
                for (final Triple<IGeneralizedRule, IGeneralizedRule, IGeneralizedRule> chaining : this.chainings) {
                    builder.append(eu.linebreak());
                    builder.append(chaining.x.export(eu));
                    builder.append(eu.tttext(" and "));
                    builder.append(eu.linebreak());
                    builder.append(chaining.y.export(eu));
                    builder.append(eu.linebreak());
                    builder.append(eu.tttext("have been merged into the new rule"));
                    builder.append(eu.linebreak());
                    builder.append(chaining.z.export(eu));
                    builder.append(eu.linebreak());
                }
            }
        }
        
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            Element sccs = CPFTag.LTS_SCC_DECOMP.create(doc);
            Iterator<IRSProblem> ltsIter = this.newProblems.iterator();
            for (Element proof : childrenProofs) {
                IRSProblem scc = ltsIter.next();
                Element locations = CPFTag.LTS_SCC.create(doc);
                Set<FunctionSymbol> fs = new HashSet<>();
                for (IGeneralizedRule rule : scc.getRules()) {
                    fs.add(rule.getRootSymbol());
                }
                for (FunctionSymbol f : fs) {
                    locations.appendChild(CPFTag.LTS_LOCATION_DUP.create(doc, f.getName()));
                }
                sccs.appendChild(CPFTag.LTS_SCC_PROOF.create(doc, locations, proof));
            }
            return sccs;
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }

    }
}
