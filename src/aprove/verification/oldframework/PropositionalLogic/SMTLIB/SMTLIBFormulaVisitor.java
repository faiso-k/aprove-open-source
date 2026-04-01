package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import aprove.verification.oldframework.PropositionalLogic.*;
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
/**
 * Interface for Formula to SMTLIB converters
 *
 * @author Andreas Kelle-Emden
 */
public interface SMTLIBFormulaVisitor extends FormulaVisitor<Object, SMTLIBTheoryAtom> {

    public Object caseSMTLIBVariable(SMTLIBVariable<?> f);

    public Object caseSMTLIBFuncApp(SMTLIBFuncApp<?> f);

    public Object caseIntConstant(SMTLIBIntConstant f);
    public Object caseIntEquals(SMTLIBIntEquals f);
    public Object caseIntGE(SMTLIBIntGE f);
    public Object caseIntGT(SMTLIBIntGT f);
    public Object caseIntLE(SMTLIBIntLE f);
    public Object caseIntLT(SMTLIBIntLT f);
    public Object caseIntUnequal(SMTLIBIntUnequal f);
    public Object caseIntITE(SMTLIBIntITE f);
    public Object caseIntMinus(SMTLIBIntMinus f);
    public Object caseIntMod(SMTLIBIntMod f);
    public Object caseIntDiv(SMTLIBIntDiv f);
    public Object caseIntMult(SMTLIBIntMult f);
    public Object caseIntPlus(SMTLIBIntPlus f);

    public Object caseRatConstant(SMTLIBRatConstant f);
    public Object caseRatEquals(SMTLIBRatEquals f);
    public Object caseRatGE(SMTLIBRatGE f);
    public Object caseRatGT(SMTLIBRatGT f);
    public Object caseRatLE(SMTLIBRatLE f);
    public Object caseRatLT(SMTLIBRatLT f);
    public Object caseRatUnequal(SMTLIBRatUnequal f);
    public Object caseRatITE(SMTLIBRatITE f);
    public Object caseRatMinus(SMTLIBRatMinus f);
    public Object caseRatMult(SMTLIBRatMult f);
    public Object caseRatPlus(SMTLIBRatPlus f);

    public Object caseBoolITE(SMTLIBBoolITE f);
    public Object caseTrue(SMTLIBBoolTrue f);
    public Object caseFalse(SMTLIBBoolFalse f);

    public Object caseBVITE(SMTLIBBVITE f);
    public Object caseBVConstant(SMTLIBBVConstant f);
    public Object caseBVConcat(SMTLIBBVConcat f);
    public Object caseBVExtract(SMTLIBBVExtract f);
    public Object caseBVNot(SMTLIBBVNot f);
    public Object caseBVNeg(SMTLIBBVNeg f);
    public Object caseBVAnd(SMTLIBBVAnd f);
    public Object caseBVOr(SMTLIBBVOr f);
    public Object caseBVXor(SMTLIBBVXor f);
    public Object caseBVSub(SMTLIBBVSub f);
    public Object caseBVAdd(SMTLIBBVAdd f);
    public Object caseBVMul(SMTLIBBVMul f);
    public Object caseBVEquals(SMTLIBBVEquals f);
    public Object caseBVGE(SMTLIBBVGE f);
    public Object caseBVGT(SMTLIBBVGT f);
    public Object caseBVLE(SMTLIBBVLE f);
    public Object caseBVLT(SMTLIBBVLT f);
    public Object caseBVUnequal(SMTLIBBVUnequal f);


}
