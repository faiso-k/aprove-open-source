package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;

/**
 * Runs through a SMT formula and checks whether it contains non-linear arithmetic.
 *
 * @author Marc Brockschmidt
 */
public class SMTLIBIsNonLinearChecker implements SMTFormulaVisitor<Object> {
    /** The result of our visits. */
    private boolean isNonLinear;

    /**
     * @return true if the checked formula is non-linear.
     */
    public boolean formulaIsNonLinear() {
        return this.isNonLinear;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseTheoryAtom(final TheoryAtom<SMTLIBTheoryAtom> f) {
        final SMTLIBTheoryAtom proposition = f.getProposition();
        proposition.apply(this);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseAnd(final AndFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
            if (this.isNonLinear) {
                break;
            }
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseConstant(final Constant<SMTLIBTheoryAtom> f) {
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIff(final IffFormula<SMTLIBTheoryAtom> f) {
        f.getArg1().apply(this);
        if (!this.isNonLinear) {
            f.getArg2().apply(this);
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIte(final IteFormula<SMTLIBTheoryAtom> f) {
        f.getCondition().apply(this);
        if (!this.isNonLinear) {
            f.getThen().apply(this);
        }
        if (!this.isNonLinear) {
            f.getElse().apply(this);
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseNot(final NotFormula<SMTLIBTheoryAtom> f) {
        f.getArg().apply(this);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseOr(final OrFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
            if (this.isNonLinear) {
                break;
            }
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseVariable(final Variable<SMTLIBTheoryAtom> f) {
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseXor(final XorFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
            if (this.isNonLinear) {
                break;
            }
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseAtLeast(final AtLeastFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
            if (this.isNonLinear) {
                break;
            }
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseAtMost(final AtMostFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
            if (this.isNonLinear) {
                break;
            }
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseCount(final CountFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
            if (this.isNonLinear) {
                break;
            }
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public void caseSMTConstant(final SMTLIBConstant<?> constant) {
        return;
    }

    /** {@inheritDoc} */
    @Override
    public void caseSMTVariable(final SMTLIBVariable<?> var) {
        return;
    }

    /** {@inheritDoc} */
    @Override
    public void caseSMTNAryFunc(final SMTLIBNAryFunc<?> nAryFunc) {
        if (!this.isNonLinear) {
            if (nAryFunc instanceof MayRequireNonLinearArithmetic) {
                this.isNonLinear |= ((MayRequireNonLinearArithmetic) nAryFunc).requiresNonLinearArithmetic();
            }
            if (nAryFunc instanceof SMTLIBIntDiv || nAryFunc instanceof SMTLIBIntMod) {
                this.isNonLinear = true;
            }
        }
        return;
    }

    /** {@inheritDoc} */
    @Override
    public void caseSMTFuncApp(final SMTLIBFuncApp<?> funcApp) {
        return;
    }

    /** {@inheritDoc} */
    @Override
    public void caseSMTITE(final SMTLIBITE<?> ite) {
        return;
    }

    /** {@inheritDoc} */
    @Override
    public void caseSMTCMP(final SMTLIBCMP<?> comparison) {
        return;
    }
}
