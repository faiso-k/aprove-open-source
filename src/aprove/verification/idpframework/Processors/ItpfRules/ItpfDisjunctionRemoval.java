package aprove.verification.idpframework.Processors.ItpfRules;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.ImplicationEngine.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ItpfDisjunctionRemoval extends IDPExportable.IDPExportableSkeleton implements GenericItpfRule<Unused>, Mark<Unused> {


    private final ImplicationEngine implicationEngine;

    @ParamsViaArguments(value = { "implicationEngine" })
    public ItpfDisjunctionRemoval(final ImplicationEngine implicationEngine) {
        this.implicationEngine = implicationEngine;
    }

    public ItpfDisjunctionRemoval() {
        this.implicationEngine = new DefaultImplicationEngine();
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>>singleton(this);
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return true;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp,
        final Itpf formula,
        final ApplicationMode mode) {
        return formula.getClauses().size() > 1;
    }

    @Override
    public boolean isComplete() {
        return false;
    }

    @Override
    public boolean isSound() {
        return true;
    }

    @Override
    public boolean isAtomicMark() {
        return false;
    }

    @Override
    public boolean isClauseMark() {
        return false;
    }

    @Override
    public boolean isContextFree() {
        return true;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        if (mark.getClass().equals(this.getClass())) {
            return this.implicationEngine.equals(((ItpfDisjunctionRemoval) mark).implicationEngine);
        } else {
            return false;
        }
    }

    @Override
    public ExecutionResult<Conjunction<Itpf>, Itpf> process(final IDPProblem idp,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) throws AbortionException {

        final LiteralMap newClause = new LiteralMap();
        final Set<ITerm<?>> newS = new LinkedHashSet<ITerm<?>>(formula.getClauses().iterator().next().getS());

        if (!executionRequirements.isComplete()) {

            for (final ItpfConjClause source : formula.getClauses()) {
                newS.retainAll(source.getS());
                for (final Map.Entry<? extends ItpfAtom, Boolean> sourceLiteral : source.getLiterals().entrySet()) {
                    boolean literalValid = true;
                    for (final ItpfConjClause precondition : formula.getClauses()) {
                        if (precondition != source) {
                            if (!this.implicationEngine.checkImplication(idp, formula.getQuantification(), precondition, sourceLiteral.getKey(), sourceLiteral.getValue(), aborter)) {
                                literalValid = false;
                                break;
                            }
                        }
                    }

                    if (literalValid) {
                        newClause.put(sourceLiteral.getKey(), sourceLiteral.getValue());
                    }
                }
            }
        }

        ExecutionResult<Conjunction<Itpf>, Itpf> result;

        if (newClause.isEmpty()) {
            result = new ExecutionResult<Conjunction<Itpf>, Itpf>(new Conjunction<Itpf>(formula), ImplicationType.EQUIVALENT, ApplicationMode.NoOp, true);
        } else {
            final ItpfFactory itpfFactory = idp.getItpfFactory();
            final Itpf newFormula = itpfFactory.create(formula.getQuantification(), itpfFactory.createClause(ImmutableCreator.create(newClause), ImmutableCreator.create(newS)));
            result = new ExecutionResult<Conjunction<Itpf>, Itpf>(new Conjunction<Itpf>(newFormula), ImplicationType.SOUND, ApplicationMode.SingleStep, true);
        }

        return result;
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        sb.append("ItpfDisjunctionRemoval");
    }

}
