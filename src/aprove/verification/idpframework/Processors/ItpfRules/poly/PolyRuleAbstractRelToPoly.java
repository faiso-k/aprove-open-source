package aprove.verification.idpframework.Processors.ItpfRules.poly;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Polynomials.Interpretation.PolyInterpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.idpframework.Processors.ItpfRules.ItpfAtomReplaceData.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class PolyRuleAbstractRelToPoly extends ContextFreeItpfReplaceRule {

    public PolyRuleAbstractRelToPoly() {
        super(new ExportableString("PolyRuleAbstractRelToPoly"), new ExportableString(
        "PolyRuleAbstractRelToPoly"));
    }

    @Override
    protected ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> processLiteral(final IDPProblem idp,
        final ReplaceContext.ReplaceContextSkeleton context,
        final ItpfAndWrapper precondition,
        final Set<ITerm<?>> s,
        final ItpfAtom atom,
        final Boolean positive,
        final ImplicationType executionRequirements,
        final ApplicationMode mode, final Abortion aborter) {
        if (atom.isItp()) {
            final ItpfItp itp = (ItpfItp) atom;

            if (itp.getRelation().isAbstract()) {
                return this.convertAbstractRelationItp(itp, positive, idp.getIdpGraph().getPolyInterpretation());
            }
        } else if (atom.isEdgeOrientation()) {
            final ItpfEdgeOrientation edgeOrientation = (ItpfEdgeOrientation) atom;

            if (edgeOrientation.getRelation().isAbstract()) {
                return this.convertAbstractRelationEdgeOrientation(idp.getIdpGraph(), edgeOrientation, positive, idp.getIdpGraph().getPolyInterpretation());
            }
        }

        return null;
    }

    private <C extends SemiRing<C>> ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> convertAbstractRelationItp(final ItpfItp itp, final boolean positive,
        final PolyInterpretation<C> polyInterpretation) {
        final Polynomial<C> polyLeft = polyInterpretation.interpretTerm(itp.getL(), itp.getKLeft(), itp.getContextL());
        final Polynomial<C> polyRight = polyInterpretation.interpretTerm(itp.getR(), itp.getKRight(), itp.getContextR());

        ConstraintType ct;
        switch (itp.getRelation()) {
        case ABSTRACT_GE:
            ct = ConstraintType.GE;
            break;
        case ABSTRACT_GT:
            ct = ConstraintType.GT;
            break;
        default: throw new UnsupportedOperationException("unknown abstract relation: " + itp.getRelation());
        }

        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

        final Polynomial<C> totalPoly = polyLeft.subtract(polyRight);
        final ItpfPolyAtom<C> polyAtom = itpfFactory.createPoly(totalPoly, ct, polyInterpretation);

        final ImmutableList<ItpfQuantor> newQuantors =
            this.getFreshVariableQuantors(itp, polyAtom, polyInterpretation, itpfFactory);


        return this.getSingletonReturn(itpfFactory, newQuantors, polyAtom, positive, ImplicationType.EQUIVALENT, ApplicationMode.SingleStep, false);
    }

    private <C extends SemiRing<C>> ExecutionResult<QuantifiedDisjunction<ItpfAtomReplaceData>, ItpfAtomReplaceData> convertAbstractRelationEdgeOrientation(final IDependencyGraph graph, final ItpfEdgeOrientation edgeOrientation, final boolean positive,
        final PolyInterpretation<C> polyInterpretation) {
        if (!positive) {
            return null;
        }

        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

        if (edgeOrientation.getRelDependency() == RelDependency.Independent) {
            this.getEmptyReturn(itpfFactory, ImplicationType.EQUIVALENT, ApplicationMode.SingleStep);
        }

        final PolyFactory polyFactory = polyInterpretation.getFactory();
        final IEdge edge = edgeOrientation.getEdge();

        final ITerm<?> fromTerm = graph.getTerm(edge.from).getSubterm(edge.fromPos).applySubstitution(edgeOrientation.getSubstitutionFrom());

        final Set<ITerm<?>> toTerms;


        if (edge.type.isInf() && edgeOrientation.getRelation() != EdgeOrientationRelation.ABSTRACT_WEAK_BOUND
                && edgeOrientation.getRelation() != EdgeOrientationRelation.ABSTRACT_COMPLEXITY_WEAK_GT) {

            toTerms = new LinkedHashSet<ITerm<?>>();
            final ITerm<?> toTerm = graph.getTerm(edge.to).applySubstitution(edgeOrientation.getSubstitutionTo());
            for (final Map.Entry<INode, ImmutableSet<IEdge>> succNodes : graph.getSuccessors(edge.to).entrySet()) {
                for (final IEdge succEdge : succNodes.getValue()) {
                    if (succEdge.type.isInf()) {
                        toTerms.add(toTerm.getSubterm(succEdge.fromPos));
                    }
                }
            }
        } else {
            toTerms = Collections.<ITerm<?>>singleton(graph.getTerm(edge.to).applySubstitution(edgeOrientation.getSubstitutionTo()));
        }

        final LiteralMap replaceCondition = new LiteralMap();
        final Set<ItpfQuantor> newQuantors = new LinkedHashSet<ItpfQuantor>();

        Polynomial<C> polyLeft = polyInterpretation.interpretTerm(fromTerm, edgeOrientation.getRelDependency(), edgeOrientation.getActiveCondition());
        newQuantors.addAll(this.getFreshVariableQuantors(fromTerm, polyLeft, polyInterpretation, itpfFactory));

        for (final ITerm<?> toTerm : toTerms) {
            Polynomial<C> polyRight = polyInterpretation.interpretTerm(toTerm, edgeOrientation.getRelDependency(), edgeOrientation.getActiveCondition());
            newQuantors.addAll(this.getFreshVariableQuantors(toTerm, polyRight, polyInterpretation, itpfFactory));

            ConstraintType ct;
            switch (edgeOrientation.getRelation()) {
            case ABSTRACT_GE:
                ct = ConstraintType.GE;
                break;
            case ABSTRACT_GT:
                ct = ConstraintType.GE;
                polyRight = polyRight.add(polyFactory.one(polyInterpretation.getRing()));
                break;
            case ABSTRACT_WEAK_GT:
                ct = ConstraintType.GE;
                polyRight = polyRight.add(polyInterpretation.getBooleanPolyVar(ConstantType.StrictOrientation, edge, edgeOrientation.getMetaData(), Collections.<Itpf>emptySet()));
                break;
            case ABSTRACT_WEAK_BOUND:
                ct = ConstraintType.GE;
                polyLeft =
                    polyLeft.mult(polyInterpretation.getBooleanPolyVar(
                        ConstantType.BoundOrientation, edge,
                        edgeOrientation.getMetaData(),
                        Collections.<Itpf> emptySet()));
                polyRight = polyInterpretation.getBoundConstantPoly();
                break;
            case ABSTRACT_STRICT_BOUND:
                ct = ConstraintType.GE;
                final Polynomial<C> boundBooleanVar = polyInterpretation.getBooleanPolyVar(ConstantType.BoundOrientation, edge, edgeOrientation.getMetaData(), Collections.<Itpf>emptySet());
                polyLeft = polyLeft.mult(boundBooleanVar);
                polyRight = polyInterpretation.getBoundConstantPoly().mult(boundBooleanVar).add(boundBooleanVar);
                break;
            case ABSTRACT_COMPLEXITY_WEAK_GT:
                ct = ConstraintType.GE;
                final C zero = polyInterpretation.getRing().zero();
                final C one = polyInterpretation.getRing().one();
                polyLeft = polyFactory.max(one, polyLeft.zero(), polyLeft.subtract(polyInterpretation.getBoundConstantPoly()));
                polyRight = polyRight.zero();

                final Set<IPosition> inspectedPositions = new LinkedHashSet<>();
                for (final Set<IEdge> succEdges : graph.getSuccessors(edge.to).values()) {
                    for (final IEdge succEdge : succEdges) {
                        if (succEdge.type.isInf() && (!inspectedPositions.contains(succEdge.fromPos))) {
                            inspectedPositions.add(succEdge.fromPos);
                            final Polynomial<C> poly =
                                polyInterpretation.interpretTerm(
                                    graph.getTerm(succEdge.from).getSubterm(succEdge.fromPos).applySubstitution(
                                        edgeOrientation.getSubstitutionTo()), edgeOrientation.getRelDependency());//RelDependency.Increasing);
                            final Polynomial<C> maxPoly = polyFactory.max(one, poly.zero(), poly.subtract(polyInterpretation.getBoundConstantPoly()));
                            polyRight = polyRight.add(maxPoly);
                        }
                    }
                }
                /*if (graph.getInDegree(edge.from, EdgeType.INF_EDGE_TYPES) == 0) {
                    IVariable<C> coeff = polyInterpretation.getNextCoeff(polyInterpretation.getRing().createUnknownVarRange());
                    polyLeft = polyLeft.mult(polyFactory.create(coeff));
                }*/
                polyRight = polyRight.add(polyInterpretation.getBooleanPolyVar(ConstantType.StrictOrientation, edge, edgeOrientation.getMetaData(), Collections.<Itpf>emptySet()));
                break;
            default: throw new UnsupportedOperationException("unknown abstract relation: " + edgeOrientation.getRelation());
            }

            final Polynomial<C> totalPoly = polyLeft.subtract(polyRight);


            final ImmutablePair<Polynomial<C>, Polynomial<C>> contextSwitches = polyInterpretation.getContextPolySwitchCoeff(edgeOrientation.getRelDependency(), edgeOrientation.getActiveCondition(), false);
            final Polynomial<C> onePoly = polyFactory.one(polyInterpretation.getRing());
            final Polynomial<C> incPoly = totalPoly.mult(onePoly.subtract(contextSwitches.y));
            final Polynomial<C> decPoly = totalPoly.mult(onePoly.subtract(contextSwitches.x)).negate();

            final ItpfPolyAtom<C> incPolyAtom = polyInterpretation.getConstraintFactory().createPoly(incPoly, ct, polyInterpretation);
            replaceCondition.put(incPolyAtom, true);
            final ItpfPolyAtom<C> decPolyAtom = itpfFactory.createPoly(decPoly, ct, polyInterpretation);
            replaceCondition.put(decPolyAtom, true);
        }

        final List<ItpfAtomReplaceData> disjunction = new ArrayList<ItpfAtomReplaceData>();
        disjunction.add(new LiteralMapData(replaceCondition, ITerm.EMPTY_SET));

        if (edgeOrientation.getRelation() == EdgeOrientationRelation.ABSTRACT_WEAK_BOUND) {
            final ItpfBoolPolyVar<C> wellFoundedVar = polyInterpretation.getItpfBooleanPolyVar(ConstantType.NatDomain, fromTerm.getDomain(), null);
            disjunction.add(new LiteralMapData(new LiteralMap(wellFoundedVar, true), ITerm.EMPTY_SET));
        }

        return this.createReplaceData(
                    ImmutableCreator.create(new ArrayList<ItpfQuantor>(newQuantors)),
                    ImmutableCreator.create(disjunction),
                    ImplicationType.EQUIVALENT,
                    ApplicationMode.SingleStep,
                    false);
    }

    private ImmutableList<ItpfQuantor> getFreshVariableQuantors(final HasVariables<?> originalAtom,
        final HasVariables<?> polyAtom,
        final PolyInterpretation<?> polyInterpretation,
        final ItpfFactory itpfFactory) {
        // check for fresh variables
        final HashSet<IVariable<?>> freshVariables = new LinkedHashSet<IVariable<?>>(polyAtom.getVariables());
        freshVariables.removeAll(originalAtom.getVariables());

        ImmutableList<ItpfQuantor> newQuantors;
        if (freshVariables.isEmpty()) {
            newQuantors = ItpfFactory.EMPTY_QUANTORS;
        } else {
            final ArrayList<ItpfQuantor> newQuant = new ArrayList<ItpfQuantor>(freshVariables.size());

            for (final IVariable<?> var : freshVariables) {
                if (!polyInterpretation.isExistQuantified(var)) {
                    newQuant.add(itpfFactory.createQuantor(true, var));
                }
            }

            newQuantors = ImmutableCreator.create(newQuant);
        }
        return newQuantors;
    }

    @Override
    public boolean isApplicable(final IDPProblem idp) {
        return idp.getIdpGraph().getPolyInterpretation() != null;
    }

    @Override
    public boolean isComplete() {
        return true;
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
        return false;
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return mark.getClass() == this.getClass();
    }
}
