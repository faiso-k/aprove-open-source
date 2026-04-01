package aprove.verification.oldframework.IntegerReasoning;


public class ExpressionConstructionStringUnparser {//extends FunctionalIntegerExpressionVisitor {

//    private final StringBuilder sb;
//
//    public ExpressionConstructionStringUnparser(final StringBuilder sb) {
//        this.sb = sb;
//    }
//
//    @Override
//    public boolean visitConstRef(final LLVMHeuristicConstRef constRef) {
//        this.sb.append("new LLVMConstRef(BigInteger.valueOf(" + constRef.getIntegerValue() + "))");
//        return true;
//    }
//
//    @Override
//    public boolean visitVarRef(final LLVMHeuristicVarRef varRef) {
//        this.sb.append("new LLVMVarRef(\"" + varRef + "\", \"" + varRef + "\")");
//        return true;
//    }
//
//    @Override
//    public boolean visitAdditionPreorder(final LLVMOperation addition) {
//        this.sb.append("LLVMOperation.create(IntArithType.ADD, ");
//        return true;
//    }
//
//    @Override
//    public boolean visitAdditionInorder(final LLVMOperation addition) {
//        this.sb.append(", ");
//        return true;
//    }
//
//    @Override
//    public boolean visitAdditionPostorder(final LLVMOperation addition) {
//        this.sb.append(")");
//        return true;
//    }
//
//    @Override
//    public boolean visitMultiplicationPreorder(final LLVMOperation multiplication) {
//        this.sb.append("LLVMOperation.create(IntArithType.MUL, ");
//        return true;
//    }
//
//    @Override
//    public boolean visitMultiplicationInorder(final LLVMOperation multiplication) {
//        this.sb.append(", ");
//        return true;
//    }
//
//    @Override
//    public boolean visitMultiplicationPostorder(final LLVMOperation multiplication) {
//        this.sb.append(")");
//        return true;
//    }
//
//    @Override
//    public boolean visitSubtractionPreorder(final LLVMOperation subtraction) {
//        this.sb.append("LLVMOperation.create(IntArithType.SUB, ");
//        return true;
//    }
//
//    @Override
//    public boolean visitSubtractionInorder(final LLVMOperation subtraction) {
//        this.sb.append(", ");
//        return true;
//    }
//
//    @Override
//    public boolean visitSubtractionPostorder(final LLVMOperation subtraction) {
//        this.sb.append(")");
//        return true;
//    }

}
