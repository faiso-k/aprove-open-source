package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.solver.Engines.SMTEngine.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatFunctions.*;
import aprove.verification.oldframework.Utility.SMTUtility.*;

/**
 * Formula visitor for propositional logic with SMT-LIB
 * theory atoms. Creates a SMTLIB2 compatible StringBuilder
 * containing one or more formulas.
 *
 * @author Marc Brockschmidt
 */
public final class SMTFormulaToSMTLIBVisitor implements SMTLIBFormulaOutputVisitor {
    /**
     * Type names for SMTLIB.
     *
     * @author Marc Brockschmidt
     */
    public static class SMTLIBTypesTranslator implements SMTTypeTranslator {
        /** {@inheritDoc} */
        @Override
        public String bitvectors(final int len) {
            return "(_ BitVec " + len + ")";
        }

        /** {@inheritDoc} */
        @Override
        public String bools() {
            return "Bool";
        }

        /** {@inheritDoc} */
        @Override
        public String integers() {
            return "Int";
        }

        /**
         * {@inheritDoc}
         * We represents rationals as reals.
         */
        @Override
        public String rationals() {
            return "Real";
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String functions(final List<String> domains, final String range) {
            throw new UnsupportedOperationException();
            // *sigh* We don't use this and the current framework doesn't give
            // the needed information.
        }
    }

    /** We will build the formula in this. */
    private final StringBuilder consString;

    /** The used logic. */
    private final SMTLogic logic;

    /**
     * This is a one-to-one mapping between our internal variables and
     * user-defined functions and the names of their representation in the
     * created SMTLIB2 problem.
     */
    private final SMTLIBVarNameMap externalToInternalVarMap;

    /**
     * The type translator used to get stuff into the SMTLIB format.
     */
    private final SMTLIBTypesTranslator typeTranslator = new SMTLIBTypesTranslator();

    /**
     * Create a new visitor. Just add a formula to get results.
     * @param l the logic used in the problem.
     */
    private SMTFormulaToSMTLIBVisitor(final SMTLogic l) {
        this.consString = new StringBuilder();
        this.externalToInternalVarMap = new SMTLIBVarNameMap();
        this.logic = l;
    }

    /**
     * Create and return a new instance of this class.
     * @param l the logic used in the problem.
     * @return a fresh formula to SMTLIB string converter.
     */
    public static SMTFormulaToSMTLIBVisitor create(final SMTLogic l) {
        return new SMTFormulaToSMTLIBVisitor(l);
    }

    /** {@inheritDoc} */
    @Override
    public String getResult() {
        final StringBuilder result = new StringBuilder();

        //First, declare what theories we use:
        if (this.logic != null) {
            result.append("(set-logic ").append(this.logic.getName()).append(")\n");
        }
        result.append("(set-info :smt-lib-version 2.0)\n");

        //Define all used variables and user-defined functions:
        for (final Entry<SMTLIBAssignableSemantics, String> e : this.externalToInternalVarMap
            .getVarToNameMap()
            .entrySet())
        {
            final String name = e.getValue();
            final SMTLIBAssignableSemantics value = e.getKey();
            if (value instanceof SMTLIBVariable<?>) {
                result
                    .append("(declare-fun ")
                    .append(name)
                    .append(" () ")
                    .append(value.getTypeAsString(this.typeTranslator))
                    .append(")\n");
            } else {
                throw new UnsupportedOperationException();
            }
        }
        result.append(this.consString);
        result.append("(check-sat)\n");
        result.append("(get-assignment)\n");
        result.append("(get-model)\n");
        result.append("(exit)\n");
        return result.toString();
    }

    /** {@inheritDoc} */
    @Override
    public void handleConstraint(final Formula<SMTLIBTheoryAtom> f) {
        this.consString.append("(assert ");
        f.apply(this);
        this.consString.append(")\n");
    }

    /** {@inheritDoc} */
    @Override
    public SMTLIBVarNameMap getVarNameMap() {
        return this.externalToInternalVarMap;
    }

    ///////////////////////////////////////////////////////////////////////////
    /////////////////////////// Propositional parts ///////////////////////////
    ///////////////////////////////////////////////////////////////////////////

    /**
     * Appends (funcName convertedArg1 ... convertedArgN) to the StringBuilder.
     * @param funcName some function name.
     * @param arguments arguments for the function.
     */
    private
        void
        caseNAryFunctionSymbol(final String funcName, final List<? extends Formula<SMTLIBTheoryAtom>> arguments)
    {
        this.consString.append("(" + funcName);
        for (final Formula<SMTLIBTheoryAtom> arg : arguments) {
            this.consString.append(" ");
            arg.apply(this);
        }
        this.consString.append(")");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseAnd(final AndFormula<SMTLIBTheoryAtom> f) {
        this.caseNAryFunctionSymbol("and", f.args);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseConstant(final Constant<SMTLIBTheoryAtom> f) {
        this.consString.append(f.getValue());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIff(final IffFormula<SMTLIBTheoryAtom> f) {
        this.consString.append("(= ");
        f.left.apply(this);
        this.consString.append(" ");
        f.right.apply(this);
        this.consString.append(")");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIte(final IteFormula<SMTLIBTheoryAtom> f) {
        this.consString.append("(ite ");
        f.condition.apply(this);
        this.consString.append(" ");
        f.thenFormula.apply(this);
        this.consString.append(" ");
        f.elseFormula.apply(this);
        this.consString.append(")");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseNot(final NotFormula<SMTLIBTheoryAtom> f) {
        this.consString.append("(not ");
        f.arg.apply(this);
        this.consString.append(")");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseOr(final OrFormula<SMTLIBTheoryAtom> f) {
        this.caseNAryFunctionSymbol("or", f.args);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseXor(final XorFormula<SMTLIBTheoryAtom> f) {
        this.caseNAryFunctionSymbol("xor", f.args);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseTheoryAtom(final TheoryAtom<SMTLIBTheoryAtom> f) {
        f.getProposition().apply(this);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseVariable(final Variable<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("Use SMTLIB variables, no propositional variables!");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseAtLeast(final AtLeastFormula<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseAtMost(final AtMostFormula<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseCount(final CountFormula<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    ///////////////////////////////////////////////////////////////////////////
    /////////////////////////////// SMTLIB parts //////////////////////////////
    ///////////////////////////////////////////////////////////////////////////

    /**
     * Appends (funcName convertedArg1 ... convertedArgN) to the StringBuilder.
     * @param funcName some function name.
     * @param arguments arguments for the function.
     */
    private void caseSMTNAryFunctionSymbol(final String funcName, final SMTLIBValue... arguments) {
        this.consString.append("(" + funcName);
        for (final SMTLIBValue argument : arguments) {
            this.consString.append(" ");
            argument.apply(this);
        }
        this.consString.append(")");
    }

    /**
     * Appends (funcName convertedArg1 ... convertedArgN) to the StringBuilder.
     * @param funcName some function name.
     * @param arguments arguments for the function.
     */
    private void caseSMTNAryFunctionSymbol(final String funcName, final List<? extends SMTLIBValue> arguments) {
        this.caseSMTNAryFunctionSymbol(funcName, arguments.toArray(new SMTLIBValue[0]));
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBoolITE(final SMTLIBBoolITE f) {
        this.caseSMTNAryFunctionSymbol("ite", f.getCondition(), f.getThenValue(), f.getElseValue());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseFalse(final SMTLIBBoolFalse f) {
        this.consString.append("false");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseTrue(final SMTLIBBoolTrue f) {
        this.consString.append("true");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntConstant(final SMTLIBIntConstant f) {
        final BigInteger value = f.getValue();
        if (value.signum() < 0) {
            this.consString.append("(- " + f.getValue().abs().toString() + ")");
        } else {
            this.consString.append(f.getValue().toString());
        }
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntEquals(final SMTLIBIntEquals f) {
        this.caseSMTNAryFunctionSymbol("=", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntGE(final SMTLIBIntGE f) {
        this.caseSMTNAryFunctionSymbol(">=", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntGT(final SMTLIBIntGT f) {
        this.caseSMTNAryFunctionSymbol(">", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntLE(final SMTLIBIntLE f) {
        this.caseSMTNAryFunctionSymbol("<=", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntLT(final SMTLIBIntLT f) {
        this.caseSMTNAryFunctionSymbol("<", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntUnequal(final SMTLIBIntUnequal f) {
        this.caseSMTNAryFunctionSymbol("distinct", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntITE(final SMTLIBIntITE f) {
        this.caseSMTNAryFunctionSymbol("ite", f.getCondition(), f.getThenValue(), f.getElseValue());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntMinus(final SMTLIBIntMinus f) {
        this.caseSMTNAryFunctionSymbol("-", f.getValues());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntMult(final SMTLIBIntMult f) {
        this.caseSMTNAryFunctionSymbol("*", f.getValues());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntMod(final SMTLIBIntMod f) {
        this.caseSMTNAryFunctionSymbol("mod", f.getValues());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntDiv(final SMTLIBIntDiv f) {
        this.caseSMTNAryFunctionSymbol("div", f.getValues());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseIntPlus(final SMTLIBIntPlus f) {
        this.caseSMTNAryFunctionSymbol("+", f.getValues());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatConstant(final SMTLIBRatConstant f) {
        BigInteger numerator = f.getValue().getNumerator();
        if (BigInteger.ZERO.equals(numerator)) {
            this.consString.append("0");
            return null;
        }
        BigInteger denominator = f.getValue().getDenominator();
        this.consString.append("(/ ");
        if (numerator.signum() < 0) {
            this.consString.append("(- " + numerator.negate().toString() + ")");
        } else {
            this.consString.append(numerator.toString());
        }
        this.consString.append(" ");
        if (denominator.signum() < 0) {
            this.consString.append("(- " + denominator.negate().toString() + ")");
        } else {
            this.consString.append(denominator.toString());
        }
        this.consString.append(")");
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatEquals(final SMTLIBRatEquals f) {
        this.caseSMTNAryFunctionSymbol("=", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatGE(final SMTLIBRatGE f) {
        this.caseSMTNAryFunctionSymbol(">=", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatGT(final SMTLIBRatGT f) {
        this.caseSMTNAryFunctionSymbol(">", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatITE(final SMTLIBRatITE f) {
        this.caseSMTNAryFunctionSymbol("ite", f.getCondition(), f.getThenValue(), f.getElseValue());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatLE(final SMTLIBRatLE f) {
        this.caseSMTNAryFunctionSymbol("<=", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatLT(final SMTLIBRatLT f) {
        this.caseSMTNAryFunctionSymbol("<", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatMinus(final SMTLIBRatMinus f) {
        this.caseSMTNAryFunctionSymbol("-", f.getValues());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatMult(final SMTLIBRatMult f) {
        this.caseSMTNAryFunctionSymbol("*", f.getValues());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatPlus(final SMTLIBRatPlus f) {
        this.caseSMTNAryFunctionSymbol("+", f.getValues());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseRatUnequal(final SMTLIBRatUnequal f) {
        this.caseSMTNAryFunctionSymbol("distinct", f.getA(), f.getB());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseSMTLIBVariable(final SMTLIBVariable<?> f) {
        final String name = this.externalToInternalVarMap.put(f, null);
        this.consString.append(name);
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseSMTLIBFuncApp(final SMTLIBFuncApp<?> f) {
        final SMTLIBFunction<?> func = f.getFunc();
        final String name = this.externalToInternalVarMap.put(func, null);
        this.caseSMTNAryFunctionSymbol(name, f.getDomVals());
        return null;
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVConstant(final SMTLIBBVConstant f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVAdd(final SMTLIBBVAdd f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVAnd(final SMTLIBBVAnd f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVConcat(final SMTLIBBVConcat f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVEquals(final SMTLIBBVEquals f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVExtract(final SMTLIBBVExtract f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVGE(final SMTLIBBVGE f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVGT(final SMTLIBBVGT f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVITE(final SMTLIBBVITE f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVLE(final SMTLIBBVLE f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVLT(final SMTLIBBVLT f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVMul(final SMTLIBBVMul f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVNeg(final SMTLIBBVNeg f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVNot(final SMTLIBBVNot f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVOr(final SMTLIBBVOr f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVSub(final SMTLIBBVSub f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVUnequal(final SMTLIBBVUnequal f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    /** {@inheritDoc} */
    @Override
    public Object caseBVXor(final SMTLIBBVXor f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }
}
