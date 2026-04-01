/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public interface GenericItpfRule<MarkMetaData> extends Immutable, ExecutableRule<Itpf, MarkMetaData>, Mark<MarkMetaData> {

    /**
     * @return True iff this rule only transforms single atoms.
     */
    public boolean isAtomicMark();

    /**
     * @return True iff this rule only makes clause-aware changes.
     */
    public boolean isClauseMark();

    /**
     * @return True iff this rule does not care about preconditions.
     */
    public boolean isContextFree();

    public static abstract class GenericItpfRuleSkeleton<MarkMetaData> extends IDPExportable.IDPExportableSkeleton implements GenericItpfRule<MarkMetaData> {

        private final ExportableString longDescription;
        private final ExportableString shortDescription;

        public GenericItpfRuleSkeleton(final ExportableString shortDescription,
            final ExportableString longDescription) {
            this.shortDescription = shortDescription;
            this.longDescription = longDescription;

            if (Globals.useAssertions) {
                assert this.isClauseMark() || !this.isAtomicMark() : "clause marks must be atomic";
                assert this.isContextFree() || !this.isAtomicMark() : "clause marks must be atomic";
            }
        }

        /**
         * Computes the result of this processor applied to a formula.
         * @param idp - the idp problem the formula belongs to
         * @param formula - the formula
         * @param aborter - the aborter, that should be checked many times against
         * timeouts/aborts, ...
         * @return The result of this processor
         * @throws AbortionException
         */
        @Override
        public final ExecutionResult<Conjunction<Itpf>, Itpf> process(final IDPProblem idp,
            final Itpf formula,
            final ImplicationType executionRequirements, final ApplicationMode mode,
            final Abortion aborter) throws AbortionException {

            final ItpfFactory itpfFactory = idp.getItpfFactory();
            final ItpfAndWrapper precondition = new ItpfAndWrapper(
                itpfFactory.create(
                    formula.getQuantification(),
                    itpfFactory.createEmptyClause()),
                itpfFactory);

            final boolean contextFree = this.isContextFree();
            final ExecutionMark<MarkMetaData> executionMark;
            if (contextFree) {
                executionMark = new ExecutionMark<MarkMetaData>(this, idp.getPolyInterpretation(), executionRequirements, mode);

                final ImmutablePair<? extends ExecutionResult<Conjunction<Itpf>, Itpf>, MarkMetaData> markContent = formula.getMarks().getMark(executionMark);
                if (markContent != null) {
                    return markContent.x;
                }
            } else {
                executionMark = null;
            }

            final TimeLogger timeLogger =
                new TimeLogger("Time to execute " + this.toString() + ":",
                    Level.FINEST, 100);

            final Itpf quantorFreeFormula = this.getQuantorFreeFormula(formula, itpfFactory);

            final ExecutionResult<Conjunction<Itpf>, Itpf> result = this.process(idp, precondition, quantorFreeFormula, executionRequirements, mode, aborter);

            final ExecutionResult<Conjunction<Itpf>, Itpf> quantifiedResult =
                this.getQuantifiedResult(result, formula, itpfFactory);

            timeLogger.log("success: " + !quantifiedResult.isSingleton(formula));

            if (contextFree) {
                MarksHandler.setExecutionMark(executionMark, formula, quantifiedResult);
            }

            return quantifiedResult;
        }

        @Override
        public final void export(final StringBuilder sb,
            final Export_Util o,
            final VerbosityLevel verbosityLevel) {
            if (verbosityLevel.compareTo(VerbosityLevel.MIDDLE) > 0) {
                sb.append(this.longDescription.export(o));
            } else {
                sb.append(this.shortDescription.export(o));
            }
        }

        private Itpf getQuantorFreeFormula(final Itpf formula,
            final ItpfFactory itpfFactory) {
            if (formula.getQuantification().isEmpty()) {
                return formula;
            } else {
                return itpfFactory.create(formula.getClauses());
            }
        }

        private ExecutionResult<Conjunction<Itpf>, Itpf> getQuantifiedResult(final ExecutionResult<Conjunction<Itpf>, Itpf> result,
            final Itpf formula,
            final ItpfFactory itpfFactory) {
            final Set<Itpf> quantifiedResults = new LinkedHashSet<Itpf>();

            for (final Itpf resultFormula : result.result) {
                final ImmutableList<ItpfQuantor> totalQuantification =
                    this.getTotalQuantification(formula, resultFormula);
                if (totalQuantification.isEmpty()) {
                    quantifiedResults.add(resultFormula);
                } else {
                    quantifiedResults.add(itpfFactory.create(totalQuantification, resultFormula.getClauses()));
                }
            }

            final ExecutionResult<Conjunction<Itpf>, Itpf> quantifiedResult =
                new ExecutionResult<Conjunction<Itpf>, Itpf> (
                        new Conjunction<Itpf>(ImmutableCreator.create(quantifiedResults)),
                        result.implication,
                        result.usedApplications,
                        result.fixpointReached
                );
            return quantifiedResult;
        }

        private ImmutableList<ItpfQuantor> getTotalQuantification(final Itpf formula,
            final Itpf resultFormula) {
            List<ItpfQuantor> totalQuantors;
            if (resultFormula.getQuantification().isEmpty()) {
                totalQuantors = formula.getQuantification();
            } else {
                totalQuantors = new ArrayList<ItpfQuantor>(formula.getQuantification());
                totalQuantors.addAll(resultFormula.getQuantification());
            }

            return ItpfUtil.cleanupQuantors(totalQuantors, resultFormula.getVariables());
        }

        protected abstract ExecutionResult<Conjunction<Itpf>, Itpf> process(final IDPProblem idp,
            final ItpfAndWrapper precondition,
            final Itpf formula,
            ImplicationType executionRequirements,
            final ApplicationMode mode, final Abortion aborter) throws AbortionException;


    }

}
