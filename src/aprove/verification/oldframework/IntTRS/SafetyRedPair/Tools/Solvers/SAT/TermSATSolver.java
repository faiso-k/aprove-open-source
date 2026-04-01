package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT;

import java.math.*;
import java.util.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.PolyConstraintsSystems.ConstraintsSystems.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.SAT.TermTools.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;

public class TermSATSolver {
    private final Abortion aborter;
    private final SMTEngine SMT_ENGINE = new SMTLIBEngine();
    private final Map<TRSTerm, YNM> SOLUTIONS = new HashMap<>();
    private final Map<TRSTerm, PolyConstraintsSystem> POLY_SYS = new HashMap<>();
    private final Map<TRSTerm, SimplePolyConstraint> POLY_CON = new HashMap<>();

    private TermSATSolver(final Abortion aborter) {
        this.aborter = aborter;
    }

    public static TermSATSolver create(final Abortion aborter) {
        return new TermSATSolver(aborter);
    }

    public boolean isUNSAT(final TRSTerm t) {
        if (this.SOLUTIONS.containsKey(t)) {
            return this.SOLUTIONS.get(t).equals(YNM.NO);
        }
        List<TRSTerm> dnf;
        try {
            dnf = TermTools.getDNF(t);
        } catch (final UnsupportedException e) {
            return false;
        }
        if (dnf.size() == 1 && dnf.get(0).equals(t)) {
            return this.checkSAT(t).equals(YNM.NO);
        } else {
            boolean isUNSAT = true;
            for (final TRSTerm c : dnf) {
                if (!this.isUNSAT(c)) {
                    isUNSAT = false;
                    break;
                }
            }
            return isUNSAT;
        }
    }

    public boolean isSAT(final TRSTerm t) {
        if (this.SOLUTIONS.containsKey(t)) {
            return this.SOLUTIONS.get(t).equals(YNM.YES);
        }
        List<TRSTerm> dnf;
        try {
            dnf = TermTools.getDNF(t);
        } catch (final UnsupportedException e) {
            return false;
        }
        if (dnf.size() == 1 && dnf.get(0).equals(t)) {
            return this.checkSAT(t).equals(YNM.YES);
        } else {
            for (final TRSTerm c : dnf) {
                if (this.isSAT(c)) {
                    return true;
                }
            }
            return false;
        }
    }

    public YNM checkSAT(final TRSTerm t) {
        YNM result;
        try {
            final List<Formula<SMTLIBTheoryAtom>> formulas = TermSATSolver.getFormulas(t);
            result =
                formulas.isEmpty() ? YNM.YES : this.SMT_ENGINE.satisfiable(formulas, SMTLogic.QF_NIA, this.aborter);
        } catch (final Exception e) {
            result = YNM.MAYBE;
        }

        this.SOLUTIONS.put(t, result);

        return result;
    }

    private static List<Formula<SMTLIBTheoryAtom>> getFormulas(final TRSTerm t) throws UnsupportedException {
        final List<Formula<SMTLIBTheoryAtom>> formulas = new ArrayList<>();
        final FormulaFactory<SMTLIBTheoryAtom> factory = new FullSharingFactory<SMTLIBTheoryAtom>();

        for (final TRSTerm atom : TermTools.getAtoms(t)) {
            if (TermTools.isFalse(atom)) {
                return Arrays.asList((Formula<SMTLIBTheoryAtom>) factory.buildTheoryAtom(SMTLIBBoolFalse.create()));
            }

            if (TermTools.isTrue(atom)) {
                continue;
            }

            try {
                formulas.add(factory.buildTheoryAtom(TermSATSolver.getSMTLIBIntCMP(atom)));
            } catch (final UnsupportedException e) {
                //
            }
        }
        return formulas;
    }

    private static SMTLIBIntCMP getSMTLIBIntCMP(final TRSTerm t) throws UnsupportedException {
        if (t instanceof TRSVariable) {
            throw new UnsupportedException("The variable " + t.toString() + " can not be transfered to SMTLIBIntCMP");
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fSymb = fApp.getRootSymbol();
        final TermTools.Function f = TermTools.Function.getFunction(fSymb); //.Function.getFunction(fSymb);

        switch (f) {
        case GT:
        case GE:
        case EQ: {
            final SMTLIBIntValue a = TermSATSolver.getSMTLIBIntValue(fApp.getArgument(0));
            final SMTLIBIntValue b = TermSATSolver.getSMTLIBIntValue(fApp.getArgument(1));
            switch (f) {
            case GT:
                return SMTLIBIntGT.create(a, b);
            case GE:
                return SMTLIBIntGE.create(a, b);
            case EQ:
                return SMTLIBIntEquals.create(a, b);
            }
        }
        case LE:
        case LT:
            final TRSTerm a = fApp.getArgument(0);
            final TRSTerm b = fApp.getArgument(1);
            TRSTerm revT = null;
            switch (f) {
            case LE:
                revT = ToolBox.buildGe(b, a);
                break;
            case LT:
                revT = ToolBox.buildGt(b, a);
                break;
            }
            return TermSATSolver.getSMTLIBIntCMP(revT);
        }
        throw new UnsupportedException("The term " + t.toString() + " can not be transfered to SMTLIBIntCMP");
    }

    private static SMTLIBIntValue getSMTLIBIntValue(final TRSTerm t) throws UnsupportedException {
        if (t instanceof TRSVariable) {
            return SMTLIBIntVariable.create(t.getName());
        }

        final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
        final FunctionSymbol fs = fApp.getRootSymbol();

        if (TermTools.Function.isInt(fs)) {
            return SMTLIBIntConstant.create(TermTools.PREDEFINED.getInt(fs, DomainFactory.INTEGERS));
        }

        final List<SMTLIBIntValue> args = new ArrayList<>(fs.getArity());

        for (final TRSTerm arg : fApp.getArguments()) {
            args.add(TermSATSolver.getSMTLIBIntValue(arg));
        }

        switch (TermTools.Function.getFunction(fs)) {
        case ADD:
            return SMTLIBIntPlus.create(args);
        case SUB:
            return SMTLIBIntMinus.create(args);
        case MUL:
            return SMTLIBIntMult.create(args);
        case DIV:
            return SMTLIBIntDiv.create(args);
        case MOD:
            return SMTLIBIntMod.create(args);
        case UMINUS:
            return SMTLIBIntMult.create(Arrays.asList(SMTLIBIntConstant.create(BigInteger.ONE.negate()), args.get(0)));
        }

        throw new UnsupportedException("The term " + t.toString() + " can not be transfered to SMTLIBIntValue");

    }

    public LinearConstraintsSystem getLinearConstraintsSystem(final TRSTerm t) throws UnsupportedException {
        try {
            return LinearConstraintsSystem.create(this.getPolyConstraintsSystem(t));
        } catch (final Exception e) {
            throw new UnsupportedException("The term " + t.toString() + " has no LinearConstraintsSystem form");
        }
    }

    /**
     * Omitting non-polynomial constraints
     */
    public PolyConstraintsSystem getPolyConstraintsSystem(final TRSTerm t) {
        if (!this.POLY_SYS.containsKey(t)) {

            List<TRSTerm> dnf;

            try {
                dnf = TermTools.getDNF(t);
                assert dnf.size() == 1;
            } catch (final Exception e) {
                return PolyConstraintsSystem.create();
            }

            final Set<SimplePolyConstraint> constraints = new HashSet<>();

            try {
                for (final TRSTerm c : TermTools.getAtoms(t)) {
                    try {
                        constraints.add(this.getSimplePolyConstraint(c));
                    } catch (final UnsupportedException e) {

                    }
                }
            } catch (final UnsupportedException e) {
                //
            }

            this.POLY_SYS.put(t, PolyConstraintsSystem.create(constraints));
        }

        return this.POLY_SYS.get(t);
    }

    private SimplePolyConstraint getSimplePolyConstraint(final TRSTerm t) throws UnsupportedException {
        if (t instanceof TRSVariable) {
            throw new UnsupportedException("The variable " + t.toString() + " has no constraint form");
        }

        if (!this.POLY_CON.containsKey(t)) {
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            final FunctionSymbol fSymb = fApp.getRootSymbol();
            final Function f = Function.getFunction(fSymb);

            switch (f) {
            case GT:
            case GE:
            case EQ: {
                final TRSTerm a = fApp.getArgument(0);
                final TRSTerm b = fApp.getArgument(1);

                final TRSTerm diff = ToolBox.buildSum(Arrays.asList(a, ToolBox.buildMinus(b)));
                final SimplePolynomial poly = TermTools.getSimplePolynomial(diff);
                ConstraintType type = null;

                switch (f) {
                case GT:
                    type = ConstraintType.GT;
                    break;
                case GE:
                    type = ConstraintType.GE;
                    break;
                case EQ:
                    type = ConstraintType.EQ;
                    break;
                }

                this.POLY_CON.put(t, new SimplePolyConstraint(poly, type));
            }
            break;

            case LE:
            case LT: {
                final TRSTerm a = fApp.getArgument(0);
                final TRSTerm b = fApp.getArgument(1);

                TRSTerm revT = null;

                switch (f) {
                case LE:
                    revT = ToolBox.buildGe(b, a);
                    break;
                case LT:
                    revT = ToolBox.buildGt(b, a);
                    break;
                }
                this.POLY_CON.put(t, this.getSimplePolyConstraint(revT));
            }
            break;
            default:
                throw new UnsupportedException("The term " + t.toString() + " has no SimplePolyConstraint form");

            }
        }

        return this.POLY_CON.get(t);
    }
}
