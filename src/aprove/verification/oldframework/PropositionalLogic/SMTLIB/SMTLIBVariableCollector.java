package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;

/**
 * Runs through a SMT formula and collects all SMT variables.
 *
 * @author Marc Brockschmidt
 */
public class SMTLIBVariableCollector implements SMTFormulaVisitor<Object> {
    /** The collected variables. */
    private final Set<SMTLIBVariable<?>> collectedVariables;

    /**
     * Create a new variable collector.
     */
    public SMTLIBVariableCollector() {
        this.collectedVariables = new LinkedHashSet<SMTLIBVariable<?>>();
    }

    /**
     * @return the collected variables.
     */
    public Set<SMTLIBVariable<?>> getCollectedVariables() {
        return this.collectedVariables;
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
        f.getArg2().apply(this);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIte(final IteFormula<SMTLIBTheoryAtom> f) {
        f.getCondition().apply(this);
        f.getThen().apply(this);
        f.getElse().apply(this);
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
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseAtLeast(final AtLeastFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseAtMost(final AtMostFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseCount(final CountFormula<SMTLIBTheoryAtom> f) {
        for (final Formula<SMTLIBTheoryAtom> arg : f.getArgs()) {
            arg.apply(this);
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
        this.collectedVariables.add(var);
    }

    /** {@inheritDoc} */
    @Override
    public void caseSMTNAryFunc(final SMTLIBNAryFunc<?> nAryFunc) {
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
