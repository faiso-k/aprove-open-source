package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;


@SuppressWarnings("javadoc")
public class VariableNode extends SimpleNumericExpressionNode {

    private final String originalId;
    private final String functionId;
    private final Type type;


    public VariableNode(
        final String text,
        final int line,
        final int position,
        final String id,
        final String functionId,
        final Type type)
    {
        super(text, line, position);
        this.originalId = type == Type.NONDET ? String.valueOf(VariableNode.getNdtCounter()) : id;

        //            type == Type.GLOBAL || type == Type.PARAMTER || type.isFunctionVar ? id : (type == Type.NONDET ? String
        //                .valueOf(getNdtCounter()) : null);
        this.functionId = type == Type.GLOBAL ? "" : functionId;
        this.type = type;
    }

    public final static String PREFIX_DELEMITER = "@";
    public final static String SUFFIX_DELEMITER = "_";

    @Override
    public String toString() {
        //        if (this.type == Type.NONDET) {
        //            return this.type.getSymbol() + this.originalId;
        //        }

        final boolean isVarPar = this.type == Type.GLOBAL || this.type == Type.PARAMTER || this.type.isFunctionVar; // == Type.VARIABLE;
        //        return this.type.getSymbol()
        //            + VariableNode.PREFIX_DELEMITER //(isVarPar ? "" : VariableNode.PREFIX_DELEMITER)
        //            + this.functionId
        //            + (isVarPar ? VariableNode.PREFIX_DELEMITER + this.originalId : "");

        if (this.type == Type.NONDET) {
            return "nondet" + VariableNode.SUFFIX_DELEMITER + "{" + this.originalId + "}";
        }

        if (this.type == Type.GLOBAL) {
            return this.originalId;
        }

        return this.originalId + (this.functionId.equals("main") ? "" : VariableNode.SUFFIX_DELEMITER + "{" + this.functionId + "}");

    }

    @Override
    public HashSet<String> getVariablesId() {
        final HashSet<String> variableId = new HashSet<>();

        if (this.originalId != null) {
            variableId.add(this.originalId);
        }

        return variableId;
    }

    public enum Type {
        //VARIABLE(""), //
        NONDET("NDT", true),
        GLOBAL("GLB", false),
        VARIABLE("VAR", true),
        //PARAMTER(""), //
        PARAMTER("PAR", false), //

        INDEX("IND", true),
        ARRAY("ARR", true),

        BRANCH("LBL", false),
        RETURN("RET", false);

        private String symbol;
        boolean isFunctionVar;

        private Type(final String s, final boolean isFuncVar) {
            this.symbol = s;

            this.isFunctionVar = isFuncVar;
        }

        public String getSymbol() {
            return this.symbol;
        }

        private static Set<String> FUNCTION_VARIABLE = null;

        public static Set<String> getFunctionVariablesPrefixes() {
            if (Type.FUNCTION_VARIABLE == null) {
                Type.FUNCTION_VARIABLE = new HashSet<>();
                for (final Type t : Type.values()) {
                    if (t.isFunctionVar) {
                        Type.FUNCTION_VARIABLE.add(t.symbol);
                    }
                }
            }

            return Type.FUNCTION_VARIABLE;
        }
    }

    public static String getPrefix(final String varId) {
        final int index = varId.indexOf(VariableNode.PREFIX_DELEMITER);

        if (index < 0) {
            return "";
        }

        return varId.substring(0, index);
    }

    public static String getFunctionId(final String varId) {
        final int index1 = varId.indexOf(VariableNode.PREFIX_DELEMITER) + 1;

        if (index1 < 1) {
            return "";
        }

        final int index2 = varId.substring(index1).indexOf(VariableNode.PREFIX_DELEMITER);

        if (index2 < 0) {
            return "";
        }

        return varId.substring(index1, index1 + index2);
    }

    public static boolean isFunctionVar(final String varId, final String functionId) {
        final String prefix = VariableNode.getPrefix(varId);

        final String funcId = VariableNode.getFunctionId(varId);

        return (funcId == functionId && Type.getFunctionVariablesPrefixes().contains(prefix));
    }

    public static boolean isVar(final String varId) {
        final String prefix = VariableNode.getPrefix(varId);

        return (Type.getFunctionVariablesPrefixes().contains(prefix));
    }

    public static boolean isNonDet(final String varId) {
        final String prefix = VariableNode.getPrefix(varId);

        return (Type.NONDET.getSymbol().equals(prefix));
    }

    public static boolean isFunctionParam(final String varId, final String functionId) {
        final String prefix = VariableNode.getPrefix(varId);

        final String funcId = VariableNode.getFunctionId(varId);

        return (funcId == functionId && Type.PARAMTER.getSymbol().equals(prefix));
        //  final String prefix = Type.PARAMTER.getSymbol() + VariableNode.PREFIX_DELEMITER + functionId;

        //  return (varId.indexOf(prefix) == 0);
    }

    public static boolean isArrayEntry(final String varId) {
        //  System.out.println("VN: " + varId);
        final String prefix = VariableNode.getPrefix(varId);

        return (Type.ARRAY.getSymbol().equals(prefix));
    }

    public static String getArrayIndex(final String varId) {
        if (!VariableNode.isArrayEntry(varId)) {
            return null;
        }

        final int index = varId.indexOf(VariableNode.PREFIX_DELEMITER);

        final String postfix = varId.substring(index);

        return Type.INDEX.getSymbol() + postfix;
    }

    //    @Override
    //    public SimplePolyFraction getPolyFraction()
    //    {
    //        final String id = this.toString();
    //        return SimplePolyFraction.create(id);
    //    }

    //    @Override
    //    public SimplePolynomial getNumeratorPolynomial()
    //    {
    //        final String id = this.toString();
    //
    //
    //        return SimplePolynomial.create(id);
    //    }
    //
    //    @Override
    //    public SimplePolynomial getDenumeratorPolynomial()
    //    {
    //        return SimplePolynomial.create(1);
    //    }
    //
    @Override
    public HashSet<String> getVariableNames() {
        final HashSet<String> variableId = new HashSet<>();

        variableId.add(this.toString());

        return variableId;
    }

    //    @Override
    //    public boolean isNonDet() {
    //        return this.type.equals(Type.NONDET);
    //    }

    public static boolean isGlobal(final String varId) {
        final String prefix = VariableNode.getPrefix(varId);

        return (Type.GLOBAL.getSymbol().equals(prefix) || Type.NONDET.getSymbol().equals(prefix));
    }

    private static int getNdtCounter() {
        return VariableNode.NDT_COUNTER++;
    }

    private static int NDT_COUNTER = 0;

    @Override
    public BooleanExpressionNode negate() {
        return new BinaryBooleanExpressionNode(this.getText() + "== 0", 0, 0, this, new ConstantNumericExpressionNode(
            "0",
            0,
            0,
            0), BinaryBooleanExpressionNode.Type.EQUAL);
    }

    @Override
    public boolean isFalse() {
        return false;
    }

    @Override
    public boolean isTrue() {
        return false;
    }

    @Override
    public HashSet<VariableNode> getNonDetVariables() {
        if (this.type.equals(Type.NONDET)) {
            return new HashSet<>(Arrays.asList(this));
        }

        return new HashSet<>();
    }

    public boolean isGlobal() {
        return this.type.equals(Type.GLOBAL);
    }

    @Override
    public TRSTerm toTerm() {
        return TRSTerm.createVariable(this.toString());
    }

    //    @Override
    //    public NumericExpressionNode negate(final int line, final int pos) {
    //        // TODO Auto-generated method stub
    //        return new BinrayNumericExpressionNode("-" + this.toString(), line, pos, new ConstantNumericExpressionNode(
    //            "1",
    //            0,
    //            0,
    //            -1), this, BinrayNumericExpressionNode.Type.MUL);
    //    }


}
