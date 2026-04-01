/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class InfRuleIdpBooleans extends InfRule {

    @Override
    public InfRuleID getID() {
        return InfRuleID.IDP_BOOLEAN;
    }

    @Override
    public String getLongName() {
        return "IDP_BOOLEAN: evaluates boolean expressions with &&, ||, not";
    }

    @Override
    public String getName() {
        return "IDP_BOOLEAN";
    }

    @Override
    public Pair<Constraint, InfProofStepInfo> applyToImplication(final Implication implication, final Abortion aborter)
        throws AbortionException
    {
        final IDPNonInfInterpretation interpretation = (IDPNonInfInterpretation) this.getIrc().getPolyInterpretation();
        if (interpretation.isNat()) {
            return null;
        }
        final Constraint newConstraint = this.doApplyToImplication(implication);
        /*
        if (newConstraint != implication) {
            System.err.println("BOOLEANS: " + implication + "\n TO: \n" + newConstraint);
        }*/
        return new Pair<>(newConstraint, null);
    }

    public Constraint doApplyToImplication(final Implication implication) {
        final IDPPredefinedMap predefinedMap =
            ((IdpInductionCalculus) this.irc).getIdp().getRuleAnalysis().getPreDefinedMap();
        for (final Constraint condition : implication.getConditions()) {
            if (condition.isReducesTo()) {
                final ReducesTo reduces = (ReducesTo) condition;
                if (!reduces.getLeft().isVariable()) {
                    final TRSFunctionApplication lhs = (TRSFunctionApplication) reduces.getLeft();
                    final FunctionSymbol lhsRoot = lhs.getRootSymbol();
                    if (reduces.getRight().isVariable()) {
                        // nothing we can do here until we define evaluation to error ;)
                        /*
                        if (PredefinedFunctions.isLand(lhsRoot) || PredefinedFunctions.isLor(lhsRoot) || PredefinedFunctions.isLnot(lhsRoot)) {
                            // split into cases true / false

                            Set<Constraint> newTrueConditions = new LinkedHashSet<Constraint>(implication.getConditions());
                            newTrueConditions.remove(condition);
                            Set<Constraint> newFalseConditions = new LinkedHashSet<Constraint>(newTrueConditions);
                            FunctionApplication TRUE = PredefinedFunctions.termTrue();
                            FunctionApplication FALSE = PredefinedFunctions.termFalse();
                            newTrueConditions.add(ReducesTo.create(lhs, TRUE, reduces.getCount(), null));
                            newFalseConditions.add(ReducesTo.create(lhs, FALSE, reduces.getCount(), null));
                            Set<Constraint> res = new LinkedHashSet<Constraint>();

                            Implication implicationTrue = Implication.create(implication.getId(), implication.getQuantor(), ConstraintSet.create(newTrueConditions), implication.getConclusion());
                            res.add((Constraint)implicationTrue.applySubstitution(Substitution.create((Variable)reduces.getRight(), TRUE)));

                            Implication implicationFalse = Implication.create(implication.getId(), implication.getQuantor(), ConstraintSet.create(newFalseConditions), implication.getConclusion());
                            res.add((Constraint)implicationFalse.applySubstitution(Substitution.create((Variable)reduces.getRight(), FALSE)));

                            return ConstraintSet.create(res);
                        }
                            */
                    } else {
                        final PredefinedFunction<? extends Domain> func = predefinedMap.getPredefinedFunction(lhsRoot);
                        if (func != null) {
                            final TRSTerm TERM_TRUE = predefinedMap.getBooleanTrue().getTerm();
                            final TRSTerm TERM_FALSE = predefinedMap.getBooleanFalse().getTerm();
                            final FunctionSymbol FS_TRUE = predefinedMap.getBooleanTrue().getSym();
                            final FunctionSymbol FS_FALSE = predefinedMap.getBooleanFalse().getSym();
                            if (func.getFunc() == Func.Eq || func.getFunc() == Func.Neq) {
                                final Boolean boolRight = PredefinedSemanticsFactory.getBoolValue(reduces.getRight());
                                if (boolRight != null) {
                                    final List<? extends IntegerDomain> dom = ((IntFunction) func).getDomains();
                                    final boolean eq = boolRight.booleanValue() ^ func.getFunc() == Func.Neq;
                                    if (eq) {
                                        final Set<Constraint> newConditions =
                                            new LinkedHashSet<Constraint>(implication.getConditions());
                                        newConditions.remove(condition);
                                        newConditions.add(ReducesTo.create(
                                            TRSTerm.createFunctionApplication(
                                                predefinedMap.getSym(Func.Ge, dom),
                                                lhs.getArguments()),
                                            TERM_TRUE,
                                            reduces.getParentFunc(),
                                            reduces.getCount(),
                                            reduces.getId()));
                                        newConditions.add(ReducesTo.create(
                                            TRSTerm.createFunctionApplication(
                                                predefinedMap.getSym(Func.Le, dom),
                                                lhs.getArguments()),
                                            TERM_TRUE,
                                            reduces.getParentFunc(),
                                            reduces.getCount(),
                                            reduces.getId()));
                                        return Implication.create(
                                            implication.getId(),
                                            implication.getQuantor(),
                                            ConstraintSet.create(newConditions),
                                            implication.getConclusion(),
                                            implication.getData());
                                    } else {
                                        final Set<Constraint> newLeftConditions =
                                            new LinkedHashSet<Constraint>(implication.getConditions());
                                        newLeftConditions.remove(condition);
                                        final Set<Constraint> newRightConditions =
                                            new LinkedHashSet<Constraint>(newLeftConditions);
                                        newLeftConditions.add(ReducesTo.create(
                                            TRSTerm.createFunctionApplication(
                                                predefinedMap.getSym(Func.Gt, dom),
                                                lhs.getArguments()),
                                            TERM_TRUE,
                                            reduces.getParentFunc(),
                                            reduces.getCount(),
                                            reduces.getId()));
                                        newRightConditions.add(ReducesTo.create(
                                            TRSTerm.createFunctionApplication(
                                                predefinedMap.getSym(Func.Lt, dom),
                                                lhs.getArguments()),
                                            TERM_TRUE,
                                            reduces.getParentFunc(),
                                            reduces.getCount(),
                                            reduces.getId()));
                                        final Set<Constraint> res = new LinkedHashSet<Constraint>();
                                        res.add(Implication.create(
                                            implication.getId(),
                                            implication.getQuantor(),
                                            ConstraintSet.create(newLeftConditions),
                                            implication.getConclusion(),
                                            implication.getData()));
                                        res.add(Implication.create(
                                            implication.getId(),
                                            implication.getQuantor(),
                                            ConstraintSet.create(newRightConditions),
                                            implication.getConclusion(),
                                            implication.getData()));
                                        return ConstraintSet.create(res);
                                    }
                                } else {
                                    // && can reduce to nothing but true or false
                                    return ConstraintSet.emptySet;
                                }
                            } else if (func.getFunc() == Func.Land) {
                                final TRSFunctionApplication rhs = (TRSFunctionApplication) reduces.getRight();
                                final FunctionSymbol rhsRoot = rhs.getRootSymbol();
                                if (FS_TRUE.equals(rhsRoot)) {
                                    final Set<Constraint> newConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newConditions.remove(condition);
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        rhs,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(1),
                                        rhs,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    return Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newConditions),
                                        implication.getConclusion(),
                                        implication.getData());
                                } else if (FS_FALSE.equals(rhsRoot)) {
                                    final Set<Constraint> newLeftConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newLeftConditions.remove(condition);
                                    final Set<Constraint> newRightConditions =
                                        new LinkedHashSet<Constraint>(newLeftConditions);
                                    newLeftConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        rhs,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    newRightConditions.add(ReducesTo.create(
                                        lhs.getArgument(1),
                                        rhs,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    final Set<Constraint> res = new LinkedHashSet<Constraint>();
                                    res.add(Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newLeftConditions),
                                        implication.getConclusion(),
                                        implication.getData()));
                                    res.add(Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newRightConditions),
                                        implication.getConclusion(),
                                        implication.getData()));
                                    return ConstraintSet.create(res);
                                } else if (predefinedMap.isLand(rhsRoot)) {
                                    final Set<Constraint> newConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newConditions.remove(condition);
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        rhs.getArgument(0),
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(1),
                                        rhs.getArgument(1),
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    return Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newConditions),
                                        implication.getConclusion(),
                                        implication.getData());
                                } else {
                                    // && can reduce to nothing but true or false
                                    return ConstraintSet.emptySet;
                                }
                            } else if (func.getFunc() == Func.Lor) {
                                final TRSFunctionApplication rhs = (TRSFunctionApplication) reduces.getRight();
                                final FunctionSymbol rhsRoot = rhs.getRootSymbol();
                                if (FS_TRUE.equals(rhsRoot)) {
                                    final Set<Constraint> newLeftConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newLeftConditions.remove(condition);
                                    final Set<Constraint> newRightConditions =
                                        new LinkedHashSet<Constraint>(newLeftConditions);
                                    newLeftConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        rhs,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    newRightConditions.add(ReducesTo.create(
                                        lhs.getArgument(1),
                                        rhs,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    final Set<Constraint> res = new LinkedHashSet<Constraint>();
                                    res.add(Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newLeftConditions),
                                        implication.getConclusion(),
                                        implication.getData()));
                                    res.add(Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newRightConditions),
                                        implication.getConclusion(),
                                        implication.getData()));
                                    return ConstraintSet.create(res);
                                } else if (FS_FALSE.equals(rhsRoot)) {
                                    final Set<Constraint> newConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newConditions.remove(condition);
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        rhs,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(1),
                                        rhs,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    return Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newConditions),
                                        implication.getConclusion(),
                                        implication.getData());
                                } else if (predefinedMap.isLor(rhsRoot)) {
                                    final Set<Constraint> newConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newConditions.remove(condition);
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        rhs.getArgument(0),
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(1),
                                        rhs.getArgument(1),
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    return Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newConditions),
                                        implication.getConclusion(),
                                        implication.getData());
                                } else {
                                    // || can reduce to nothing else
                                    return ConstraintSet.emptySet;
                                }
                            } else if (func.getFunc() == Func.Lnot) {
                                final TRSFunctionApplication rhs = (TRSFunctionApplication) reduces.getRight();
                                final FunctionSymbol rhsRoot = rhs.getRootSymbol();
                                if (FS_TRUE.equals(rhsRoot)) {
                                    final Set<Constraint> newConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newConditions.remove(condition);
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        TERM_FALSE,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    return Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newConditions),
                                        implication.getConclusion(),
                                        implication.getData());
                                } else if (FS_FALSE.equals(rhsRoot)) {
                                    final Set<Constraint> newConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newConditions.remove(condition);
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        TERM_TRUE,
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    return Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newConditions),
                                        implication.getConclusion(),
                                        implication.getData());
                                } else if (predefinedMap.isLnot(rhsRoot)) {
                                    final Set<Constraint> newConditions =
                                        new LinkedHashSet<Constraint>(implication.getConditions());
                                    newConditions.remove(condition);
                                    newConditions.add(ReducesTo.create(
                                        lhs.getArgument(0),
                                        rhs.getArgument(0),
                                        reduces.getParentFunc(),
                                        reduces.getCount(),
                                        reduces.getId()));
                                    return Implication.create(
                                        implication.getId(),
                                        implication.getQuantor(),
                                        ConstraintSet.create(newConditions),
                                        implication.getConclusion(),
                                        implication.getData());
                                } else {
                                    // ! can reduce to nothing but true or false
                                    return ConstraintSet.emptySet;
                                }
                            }
                        }
                    }
                }
            }
        }
        return implication;
    }

}
