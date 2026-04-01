package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

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
 * theory atoms. Creates a YICES compatible StringBuilder
 * containing one or more formulas.
 *
 * @author Andreas Kelle-Emden
 */
public class SMTFormulaToYICESVisitor implements SMTLIBFormulaOutputVisitor {

    private final StringBuilder consString;
    // While visiting the formula, collect the variables
    // and store them in this map
    private final Map<SMTLIBAssignableSemantics, String> varMap;
    private final SMTLIBVarNameMap yicesNames;

    private final YicesTypeTranslator types;

    private SMTFormulaToYICESVisitor() {
        this.consString = new StringBuilder();
        this.varMap = new LinkedHashMap<SMTLIBAssignableSemantics, String>();
        this.types = new YicesTypeTranslator();
        this.yicesNames = new SMTLIBVarNameMap();
    }

    /**
     * Create and return a new instance of this class.
     */
    public static SMTFormulaToYICESVisitor create() {
        return new SMTFormulaToYICESVisitor();
    }

    /**
     * Return the resulting string that was build up to now.
     */
    @Override
    public String getResult() {
        final StringBuilder result = new StringBuilder();

        for (final Map.Entry<SMTLIBAssignableSemantics, String> e: this.varMap.entrySet()) {
            result.append("(define ");
            result.append(this.yicesNames.get(e.getKey()));
            result.append("::");
            result.append(e.getValue());
            result.append(")\n");
        }
        result.append(this.consString);
        result.append("(check)\n");
        return result.toString();
    }


    /** {@inheritDoc} */
    @Override
    public SMTLIBVarNameMap getVarNameMap() {
        return this.yicesNames;
    }

    /**
     * Add a constraint given as a formula.
     */
    @Override
    public void handleConstraint(final Formula<SMTLIBTheoryAtom> f) {
        this.consString.append("(assert ");
        f.apply(this);
        this.consString.append(")\n");
    }

    // Propositional parts

    @Override
    public Object caseAnd(final AndFormula<SMTLIBTheoryAtom> f) {
        this.consString.append("(and");
        for (final Formula<SMTLIBTheoryAtom> arg : f.args) {
            this.consString.append(" ");
            arg.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseConstant(final Constant<SMTLIBTheoryAtom> f) {
        this.consString.append(f.getValue());
        return null;
    }

    @Override
    public Object caseIff(final IffFormula<SMTLIBTheoryAtom> f) {
        this.consString.append("(= ");
        f.left.apply(this);
        this.consString.append(" ");
        f.right.apply(this);
        this.consString.append(")");
        return null;
    }

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

    @Override
    public Object caseNot(final NotFormula<SMTLIBTheoryAtom> f) {
        this.consString.append("(not ");
        f.arg.apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseOr(final OrFormula<SMTLIBTheoryAtom> f) {
        this.consString.append("(or");
        for (final Formula<SMTLIBTheoryAtom> arg : f.args) {
            this.consString.append(" ");
            arg.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseTheoryAtom(final TheoryAtom<SMTLIBTheoryAtom> f) {
        f.getProposition().apply(this);
        return null;
    }

    @Override
    public Object caseVariable(final Variable<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("Use SMTLIB variables, no propositional variables!");
    }

    @Override
    public Object caseXor(final XorFormula<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("No XOR in YICES!");
    }

    // Linear integer arithmetic parts

    @Override
    public Object caseIntConstant(final SMTLIBIntConstant f) {
        this.consString.append(f.getValue().toString());
        return null;
    }

    @Override
    public Object caseIntEquals(final SMTLIBIntEquals f) {
        this.consString.append("(= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntGE(final SMTLIBIntGE f) {
        this.consString.append("(>= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntGT(final SMTLIBIntGT f) {
        this.consString.append("(> ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntLE(final SMTLIBIntLE f) {
        this.consString.append("(<= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntLT(final SMTLIBIntLT f) {
        this.consString.append("(< ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }


    @Override
    public Object caseIntUnequal(final SMTLIBIntUnequal f) {
        this.consString.append("(/= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntITE(final SMTLIBIntITE f) {
        this.consString.append("(ite ");
        f.getCondition().apply(this);
        this.consString.append(" ");
        f.getThenValue().apply(this);
        this.consString.append(" ");
        f.getElseValue().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntMinus(final SMTLIBIntMinus f) {
        this.consString.append("(-");
        for (final SMTLIBIntValue v : f.getValues()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntMult(final SMTLIBIntMult f) {
        this.consString.append("(*");
        for (final SMTLIBIntValue v : f.getValues()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntMod(final SMTLIBIntMod f) {
        this.consString.append("(mod");
        for (final SMTLIBIntValue v : f.getValues()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntDiv(final SMTLIBIntDiv f) {
        this.consString.append("(div");
        for (final SMTLIBIntValue v : f.getValues()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseIntPlus(final SMTLIBIntPlus f) {
        this.consString.append("(+");
        for (final SMTLIBIntValue v : f.getValues()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatConstant(final SMTLIBRatConstant f) {
        this.consString.append(f.getValue().toString());
        return null;
    }

    @Override
    public Object caseRatEquals(final SMTLIBRatEquals f) {
        this.consString.append("(= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatGE(final SMTLIBRatGE f) {
        this.consString.append("(>= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatGT(final SMTLIBRatGT f) {
        this.consString.append("(> ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatITE(final SMTLIBRatITE f) {
        this.consString.append("(ite ");
        f.getCondition().apply(this);
        this.consString.append(" ");
        f.getThenValue().apply(this);
        this.consString.append(" ");
        f.getElseValue().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatLE(final SMTLIBRatLE f) {
        this.consString.append("(<= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatLT(final SMTLIBRatLT f) {
        this.consString.append("(< ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatMinus(final SMTLIBRatMinus f) {
        this.consString.append("(-");
        for (final SMTLIBRatValue v : f.getValues()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatMult(final SMTLIBRatMult f) {
        this.consString.append("(*");
        for (final SMTLIBRatValue v : f.getValues()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatPlus(final SMTLIBRatPlus f) {
        this.consString.append("(+");
        for (final SMTLIBRatValue v : f.getValues()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseRatUnequal(final SMTLIBRatUnequal f) {
        this.consString.append("(/= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseSMTLIBVariable(final SMTLIBVariable<?> f) {
        // old version: String name = "var_"+f.getName();
        this.varMap.put(f, f.getTypeAsString(this.types));
        final String name = this.yicesNames.put(f, null);
        this.consString.append(name);
        return null;
    }


    @Override
    public Object caseSMTLIBFuncApp(final SMTLIBFuncApp<?> f) {
        final SMTLIBFunction<?> func = f.getFunc();
        final StringBuilder result = new StringBuilder();
        result.append("(-> ");
        for (final String s: func.getDomains()) {
            result.append(s);
            result.append(" ");
        }
        result.append(func.getRange(this.types));
        result.append(")");
        // old version: String name = "func_"+func.getName();
        this.varMap.put(func, result.toString());
        final String name = this.yicesNames.put(func, null);

        this.consString.append("(");
        this.consString.append(name);
        for (final SMTLIBValue v : f.getDomVals()) {
            this.consString.append(" ");
            v.apply(this);
        }
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVConstant(final SMTLIBBVConstant f) {
        this.consString.append("(mk-bv ");
        this.consString.append(f.getLen());
        this.consString.append(" ");
        this.consString.append(f.getValue());
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBoolITE(final SMTLIBBoolITE f) {
        this.consString.append("(ite ");
        f.getCondition().apply(this);
        this.consString.append(" ");
        f.getThenValue().apply(this);
        this.consString.append(" ");
        f.getElseValue().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVAdd(final SMTLIBBVAdd f) {
        this.consString.append("(bv-add ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVAnd(final SMTLIBBVAnd f) {
        this.consString.append("(bv-and ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVConcat(final SMTLIBBVConcat f) {
        this.consString.append("(bv-concat ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVEquals(final SMTLIBBVEquals f) {
        this.consString.append("(= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVExtract(final SMTLIBBVExtract f) {
        this.consString.append("(bv-extract ");
        f.getA().apply(this);
        this.consString.append(" ");
        this.consString.append(f.getI());
        this.consString.append(" ");
        this.consString.append(f.getJ());
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVGE(final SMTLIBBVGE f) {
        this.consString.append("(bv-ge ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVGT(final SMTLIBBVGT f) {
        this.consString.append("(bv-gt ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVITE(final SMTLIBBVITE f) {
        this.consString.append("(ite ");
        f.getCondition().apply(this);
        this.consString.append(" ");
        f.getThenValue().apply(this);
        this.consString.append(" ");
        f.getElseValue().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVLE(final SMTLIBBVLE f) {
        this.consString.append("(bv-le ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVLT(final SMTLIBBVLT f) {
        this.consString.append("(bv-lt ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVMul(final SMTLIBBVMul f) {
        this.consString.append("(bv-mul ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVNeg(final SMTLIBBVNeg f) {
        this.consString.append("(bv-neg ");
        f.getA().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVNot(final SMTLIBBVNot f) {
        this.consString.append("(bv-not ");
        f.getA().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVOr(final SMTLIBBVOr f) {
        this.consString.append("(bv-or ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVSub(final SMTLIBBVSub f) {
        this.consString.append("(bv-sub ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVUnequal(final SMTLIBBVUnequal f) {
        this.consString.append("(/= ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseBVXor(final SMTLIBBVXor f) {
        this.consString.append("(bv-xor ");
        f.getA().apply(this);
        this.consString.append(" ");
        f.getB().apply(this);
        this.consString.append(")");
        return null;
    }

    @Override
    public Object caseFalse(final SMTLIBBoolFalse f) {
        this.consString.append("false");
        return null;
    }

    @Override
    public Object caseTrue(final SMTLIBBoolTrue f) {
        this.consString.append("true");
        return null;
    }







    /**
     * Type names for YICES
     *
     * @author Andreas Kelle-Emden
     */
    public static class YicesTypeTranslator implements SMTTypeTranslator {

        @Override
        public String bitvectors(final int len) {
            return "(bitvector "+len+")";
        }

        @Override
        public String bools() {
            return "bool";
        }

        @Override
        public String integers() {
            return "int";
        }

        /**
         * rationals are presented as reals, as rat subset real
         */
        @Override
        public String rationals() {
            return "real";
        }

        @Override
        public String functions(final List<String> domains, final String range) {
            final StringBuilder result = new StringBuilder();
            result.append("(-> ");
            for (final String s: domains) {
                result.append(s);
                result.append(" ");
            }
            result.append(range);
            result.append(")");
            return result.toString();
        }

    }

    @Override
    public Object caseAtLeast(final AtLeastFormula<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public Object caseAtMost(final AtMostFormula<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public Object caseCount(final CountFormula<SMTLIBTheoryAtom> f) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }


}
