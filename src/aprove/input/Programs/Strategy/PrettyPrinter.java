package aprove.input.Programs.Strategy;

import java.util.*;

public class PrettyPrinter implements StrategyElementVisitor {
    private static interface SpecialPrinter {
        void print(GenericExpression expr);
    }

    private class InfixPrinter implements SpecialPrinter {
        private final String infix;
        public InfixPrinter(String infix) {
            this.infix = infix;
        }
        @Override
        public void print(GenericExpression expr) {
            assert expr.params.params.isEmpty();
            assert expr.subexpressions.exps.size() == 2;

            expr.subexpressions.exps.get(0).accept(PrettyPrinter.this);
            PrettyPrinter.this.state.appendOperator(this.infix);
            expr.subexpressions.exps.get(1).accept(PrettyPrinter.this);
        }
    }

    private class PostfixPrinter implements SpecialPrinter {
        private final String postfix;
        public PostfixPrinter(String postfix) {
            this.postfix = postfix;
        }
        @Override
        public void print(GenericExpression expr) {
            assert expr.params.params.isEmpty();
            assert expr.subexpressions.exps.size() == 1;

            expr.subexpressions.exps.get(0).accept(PrettyPrinter.this);
            PrettyPrinter.this.state.appendSeperator(this.postfix);
        }
    }

    private PrettyPrintState2 state = new PrettyPrintState2();

    private Map<String, SpecialPrinter> specialExpressions = new HashMap<String, SpecialPrinter>();

    public PrettyPrinter() {
        this.specialExpressions.put("_Sequence", new InfixPrinter(":"));
        this.specialExpressions.put("_ParallelSequence", new InfixPrinter(";"));
        this.specialExpressions.put("_Star", new PostfixPrinter("*"));
        this.specialExpressions.put("_Plus", new PostfixPrinter("+"));
        this.specialExpressions.put("_Question", new PostfixPrinter("?"));
    }

    @Override
    public void visit(RawModule rawModule) {
        for(Map.Entry<String, String> e: rawModule.imports.entrySet()) {
            this.state.appendWord("import");
            this.state.appendWord(e.getKey());
            this.state.appendWord("as");
            this.state.appendWord(e.getValue());
            this.state.recordSeperator();
        }
        for(Declaration decl: rawModule.namespace) {
            decl.accept(this);
            this.state.recordSeperator();
        }
    }

    @Override
    public void visit(ClassDeclaration decl) {
        this.state.appendWord("declare");
        this.state.appendWord(decl.name);
        this.state.appendOperator("=");
        this.state.appendWord(decl.classname);
        if (decl.defaults != null && ! decl.defaults.params.isEmpty()) {
            this.state.appendWord("defaults");
            decl.defaults.accept(this);
        }
    }

    @Override
    public void visit(LetDeclaration decl) {
        this.state.appendWord("let");
        this.state.appendWord(decl.name);
        this.state.appendWord("=");
        decl.body.accept(this);
    }

    @Override
    public Void visit(FunctionExpression expr) {
        this.state.appendWord(expr.name);
        return null;
    }

    @Override
    public Void visit(GenericExpression expr) {
        SpecialPrinter special = this.specialExpressions.get(expr.name);
        if (special != null) {
            special.print(expr);
        } else {
            this.state.appendWord(expr.name);
            expr.params.accept(this);
            expr.subexpressions.accept(this);
        }
        return null;
    }

    @Override
    public void visit(Parameters params) {
        if (params.params.isEmpty()) {
            return;
        }
        boolean middle = false;
        this.state.startGroup("[");
        for (Map.Entry<String, Value> e : params.params.entrySet()) {
            if (middle) {
                this.state.appendSeperator(",");
            }
            middle = true;
            this.state.appendWord(e.getKey());
            this.state.appendOperator("=");
            e.getValue().accept(this);
        }
        this.state.endGroup("]");
    }

    @Override
    public void visit(ExpressionList exprs) {
        if (exprs.exps.isEmpty()) {
            return;
        }
        boolean middle = false;
        this.state.startGroup("(");
        for (StrategyExpression expr: exprs.exps) {
            if (middle) {
                this.state.appendSeperator(",");
            }
            middle = true;
            expr.accept(this);
        }
        this.state.endGroup(")");
    }

    @Override
    public Void visit(StringValue val) {
        this.state.appendWord("\"" + val.value + "\"");
        return null;
    }

    @Override
    public Void visit(NumberValue val) {
        this.state.appendWord(val.value.toString());
        return null;
    }

    @Override
    public Void visit(ComplexValue val) {
        this.state.appendWord(val.identifier);
        val.params.accept(this);
        return null;
    }

    public String getContents() {
        return this.state.getContents();
    }
}
