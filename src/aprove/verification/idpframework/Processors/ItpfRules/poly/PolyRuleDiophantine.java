package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.poly.PolyRuleDiophantine.*;
import aprove.verification.idpframework.Processors.Poly.*;
import immutables.*;

/**
 * @author MP
 */
public class PolyRuleDiophantine extends AbstractItpfReplaceRule.ItpfReplaceRuleSkeleton<PreconditionToVarSignumCache, Unused> {

    private final BigIntSMTEngine smtEngine = new BigIntSMTEngine();

    public PolyRuleDiophantine() {
        super(new ExportableString("[P] Diophantine"), new ExportableString("[P] Diophantine"));
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp,
        final Itpf formula,
        final ApplicationMode mode) {
        return this.isApplicable(idp);
    }

    @Override
    public Collection<? extends Mark<?>> getUsedMarks() {
        return Collections.<Mark<?>> singleton(this);
    }

    @Override
    public boolean isComplete() {
        return true;
    }

    @Override
    public boolean isSound() {
        return false;
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
        return false;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return mark.getClass() == this.getClass();
    }

    @Override
    protected PreconditionToVarSignumCache createContext(final IDPProblem idp,
        final ItpfAndWrapper precondition,
        final Itpf formula,
        final ImplicationType executionRequirements,
        final ApplicationMode mode,
        final Abortion aborter) {
        return new PreconditionToVarSignumCache();
    }

    @Override
    protected ExecutionResult<? extends QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final PreconditionToVarSignumCache context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) throws AbortionException {

        if (atom.isPoly() && !executionRequirements.isSound()) {
            final ItpfPolyAtom<BigInt> polyAtom = (ItpfPolyAtom<BigInt>) atom;
            final PolyInterpretation<BigInt> polyInterpretation = (PolyInterpretation<BigInt>) idp.getIdpGraph().getPolyInterpretation();

            final Map<IVariable<BigInt>, Signum> varSignum = this.determineVarSignum(polyInterpretation, context, precondition.getFormula(), aborter);

            if (polyAtom.getConstraintType() != ConstraintType.EQ || positive) {
                final DiophantineSplit<BigInt> diophantineSplit =
                    DiophantineSplit.create(polyInterpretation, precondition.getTotalQuantification(),
                        polyAtom.getPoly());

                final LiteralMap newLiterals = new LiteralMap();

                final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

                for (final Map.Entry<ImmutableMap<IVariable<BigInt>, BigInt>, Polynomial<BigInt>> diophantineConstraint : diophantineSplit.getSplit().entrySet()) {
                    final Signum universalSignum =
                        Signum.getSignum(varSignum, diophantineConstraint.getKey());
                    Polynomial<BigInt> poly;
                    ConstraintType ct;
                    if (universalSignum != Signum.Zero) {
                        if (polyAtom.getConstraintType() == ConstraintType.EQ) {
                            poly = diophantineConstraint.getValue();
                            ct = ConstraintType.EQ;
                        } else {
                            if (universalSignum.isPos() && positive
                                || universalSignum.isNeg() && !positive) {
                                poly = diophantineConstraint.getValue();
                                ct = ConstraintType.GE;
                            } else if (universalSignum.isPos() && !positive
                                || universalSignum.isNeg() && positive) {
                                poly =
                                    diophantineConstraint.getValue().negate();
                                ct = ConstraintType.GE;
                            } else {
                                poly = diophantineConstraint.getValue();
                                ct = ConstraintType.EQ;
                            }
                        }

                        newLiterals.put(
                            itpfFactory.createPoly(poly, ct, polyInterpretation),
                            true);

    //                    System.err.println("SPLIT " + poly.getFactory().createMonomial(poly.getRing(), ImmutableCreator.create(diophantineConstraint.getKey())) + " : " + poly + " " + ct);
                    }
                }

                return this.createReplaceData(itpfFactory, ItpfFactory.EMPTY_QUANTORS, newLiterals, ImplicationType.COMPLETE, ApplicationMode.SingleStep, false);
            }
        }
        return null;
    }

    private Map<IVariable<BigInt>, Signum> determineVarSignum(final PolyInterpretation<BigInt> interpretation,
        final PreconditionToVarSignumCache context, final Itpf precondition,
        final Abortion aborter) throws AbortionException {
        Map<IVariable<BigInt>, Signum> result = context.get(precondition);
        if (result != null) {
            return result;
        }

        final Iterator<ItpfConjClause> clausesIterator =
            precondition.getClauses().iterator();

        result = new LinkedHashMap<IVariable<BigInt>, Signum>();

        // initialize result
        if (clausesIterator.hasNext()) {
            result.putAll(this.smtEngine.getVarSignum(clausesIterator.next(),
                interpretation, aborter));
        }

        // just keep intersection of var signums
        if (clausesIterator.hasNext() && !result.isEmpty()) {
            final Map<IVariable<BigInt>, Signum> clauseVarSignum = this.smtEngine.getVarSignum(clausesIterator.next(),
                interpretation, aborter);
            final Iterator<Entry<IVariable<BigInt>, Signum>> resultIterator =
                result.entrySet().iterator();

            while (resultIterator.hasNext()) {
                final Entry<IVariable<BigInt>, Signum> resultSignumEntry = resultIterator.next();
                final Signum clauseSignum = clauseVarSignum.get(resultSignumEntry.getKey());
                if (clauseSignum != null) {
                    resultSignumEntry.setValue(clauseSignum.lessSpecific(resultSignumEntry.getValue()));
                } else {
                    resultIterator.remove();
                }
            }
        }

        context.put(precondition, result);

        return result;
    }

    protected static class PreconditionToVarSignumCache extends ReplaceContext.ReplaceContextSkeleton {

        private final HashMap<Itpf, Map<IVariable<BigInt>, Signum>> cache;

        public PreconditionToVarSignumCache() {
            this.cache = new HashMap<Itpf, Map<IVariable<BigInt>, Signum>>();
        }

        public Map<IVariable<BigInt>, Signum> get(final Itpf precondition) {
            return this.cache.get(precondition);
        }

        public void put(final Itpf precondition, final Map<IVariable<BigInt>, Signum> result) {
            this.cache.put(precondition, result);
        }

    }

}
