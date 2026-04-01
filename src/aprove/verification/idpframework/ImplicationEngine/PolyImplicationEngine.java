package aprove.verification.idpframework.ImplicationEngine;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Itpf.ItpfPolyAtom.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.poly.*;
import aprove.verification.idpframework.Processors.NonInf.Solving.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class PolyImplicationEngine extends ImplicationEngine.ImplicationEngineSkeleton {

    @Override
    public boolean checkImplication(final IDPProblem idp,
        final List<ItpfQuantor> quantification,
        final ItpfConjClause precondition,
        final Disjunction<ItpfConjClause> conclusion,
        final Abortion aborter) throws AbortionException {

//        if (conclusion.isPoly()) {
//            final ItpfPolyAtom<?> polyConclusion = (ItpfPolyAtom<?>) conclusion;
//            if (polyConclusion.getInterpretation().getFactory().getRing() instanceof BigInt) {
//                return checkBigIntImplication(idp, precondition, (ItpfPolyAtom<BigInt>) polyConclusion, positive, (PolyInterpretation<BigInt>) polyConclusion.getInterpretation(), aborter);
//            }
//        }
        return false;
    }

    private boolean checkBigIntImplication(final IDPProblem idp, final ImmutableList<ItpfQuantor> quantifications, final ItpfConjClause precondition,
        final ItpfPolyAtom<BigInt> polyConclusion,
        final boolean positive,
        final PolyInterpretation<BigInt> polyInterpretation, final Abortion aborter) throws AbortionException {

        final Set<ItpfConjClause> clauses = new LinkedHashSet<ItpfConjClause>();
        if (positive) {
            final ItpfConjClause constraint = this.createConstraint(polyInterpretation, quantifications, precondition, polyConclusion, aborter);
            clauses.add(constraint);
        } else {
            for (final ItpfPolyAtom<BigInt> negatedConclusion : polyConclusion.negate()) {
                final ItpfConjClause constraint = this.createConstraint(polyInterpretation, quantifications, precondition, negatedConclusion, aborter);
                clauses.add(constraint);
            }
        }

        final ItpfPolyDiophantineSatSolver solver = new ItpfPolyDiophantineSatSolver();

        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

        final PolyInterpretation<BigInt> solution = solver.solve(idp.getPredefinedMap(),
            polyInterpretation,
            new Conjunction<Itpf>(
                    itpfFactory.create(ItpfFactory.EMPTY_QUANTORS, ImmutableCreator.create(clauses))),
            aborter);

        return solution != null;
    }

    private ItpfConjClause createConstraint(final PolyInterpretation<BigInt> polyInterpretation, final ImmutableList<ItpfQuantor> quantifications, final ItpfConjClause precondition, final ItpfPolyAtom<BigInt> polyConclusion, final Abortion aborter) throws AbortionException {
        final Pair<Set<ItpfPolyAtom<BigInt>>, ItpfPolyAtom<BigInt>> unconditional =
            PolyRuleConditionalToUnconditional.processPolyConclusion(PolyRuleConditionalToUnconditional.getPolynomialPreconditions(precondition, polyInterpretation), polyConclusion, polyInterpretation, PolyRuleConditionalToUnconditional.SearchMode.FULL, true, aborter);


        final LiteralMap newLiterals = new LiteralMap();
        final ItpfFactory itpfFactory = polyInterpretation.getConstraintFactory();

        for (final ItpfPolyAtom<BigInt> polyAtom : unconditional.x) {

            final Polynomial<BigInt> poly = polyAtom.getPoly();
            final DiophantineSplit<BigInt> diophantineSplit = DiophantineSplit.create(polyInterpretation, quantifications, poly);

            for (final Polynomial<BigInt> diophantineConstraint : diophantineSplit.getSplit().values()) {
                newLiterals.put(itpfFactory.createPoly(diophantineConstraint, ConstraintType.EQ, polyInterpretation), true);
            }
        }

        return itpfFactory.createClause(ImmutableCreator.create(newLiterals), ITerm.EMPTY_SET);
    }


}
