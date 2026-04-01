package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.Program.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

/** Converts a Term into a String.
 * @author nowonder
 * @version $Id$
 */
public class ToACL2Visitor implements CoarseGrainedTermVisitor<StringBuffer> {

    public static final String INDENT_STRING = "  ";

    StringBuffer sb;
    int indent;
    FreshNameGenerator fng;
    RuleInfo ruleInfo;
    boolean fullLists;

    @Override
    public StringBuffer caseVariable(AlgebraVariable v) {
        if (this.ruleInfo == null || this.ruleInfo.getVarNum(v) == null) {
            this.sb.append(this.fng.getFreshName(v.getName(),true));
        } else {
            int oldIndent = this.indent;
            int varNum = this.ruleInfo.getVarNum(v);
            List<Integer> argNums = new ArrayList<Integer>(this.ruleInfo.getArgNum(v));
            List<Boolean> argLasts = new ArrayList<Boolean>(this.ruleInfo.getArgLast(v));
            while (!argNums.isEmpty()) {
                int argNum = argNums.get(0);
                boolean last = argLasts.get(0);
                argNums.remove(0);
                argLasts.remove(0);
                if (this.fullLists || !last) {
                    this.indent("car");
                }
                for (int j = 0; j <= argNum; j++) {
                    this.indent("cdr");
                }
            }
            this.sb.append("x");
            this.sb.append(varNum);
            while (this.indent > oldIndent) {
                this.dedent();
            }
        }
        return this.sb;
    }

    @Override
    public StringBuffer caseFunctionApp(AlgebraFunctionApplication f) {
        SyntacticFunctionSymbol fsym =  (SyntacticFunctionSymbol)f.getSymbol();
        if (this.fullLists) {
            List<AlgebraTerm> args = f.getArguments();
            String prefix = fsym instanceof ConstructorSymbol ? "list '" : "";
            this.preindent(prefix+this.fng.getFreshName(fsym.getName(),true));
            for (AlgebraTerm arg : args) {
                this.level();
                arg.apply(this);
            }
            this.dedent();
        } else {
            if (fsym.getArity() == 0) {
                this.sb.append("'");
                this.sb.append(this.fng.getFreshName(fsym.getName(),true));
            } else {
                List<AlgebraTerm> args = f.getArguments();
                if (fsym instanceof ConstructorSymbol) {
                    int oldIndent = this.indent;
                    this.indent("cons");
                    this.sb.append("'");
                    this.sb.append(this.fng.getFreshName(fsym.getName(),true));
                    this.level();
                    for (int i = 0; i+1 < fsym.getArity(); i++) {
                        this.indent("cons");
                        args.get(i).toACL2(this.sb, this.indent, this.fng, this.ruleInfo, this.fullLists);
                    }
                    this.level();
                    args.get(args.size()-1).toACL2(this.sb, this.indent, this.fng, this.ruleInfo, this.fullLists);
                    while (this.indent > oldIndent) {
                        this.dedent();
                    }
                } else {
                    this.preindent(this.fng.getFreshName(fsym.getName(),true));
                    for (AlgebraTerm arg : args) {
                        this.level();
                        arg.apply(this);
                    }
                    this.dedent();
                }
            }
        }
        return this.sb;
    }

    private void indent(String head) {
        this.preindent(head);
        this.level();
    }

    private void preindent(String head) {
        this.sb.append("(");
        this.sb.append(head);
        this.indent++;
    }

    private void dedent() {
        this.indent--;
        this.level();
        this.sb.append(")");
    }

    private void level() {
        this.sb.append("\n");
        for (int i = 0; i < this.indent; i++) {
            this.sb.append(ToACL2Visitor.INDENT_STRING);
        }
    }

    public ToACL2Visitor(StringBuffer sb, int indent, FreshNameGenerator fng, RuleInfo ruleInfo, boolean fullLists) {
        this.sb = sb;
        this.indent = indent;
        this.fng = fng;
        this.ruleInfo = ruleInfo;
        this.fullLists = fullLists;
    }

    public static void apply(AlgebraTerm t, StringBuffer sb, int indent, FreshNameGenerator fng, RuleInfo ruleInfo, boolean fullLists) {
        t.apply(new ToACL2Visitor(sb, indent, fng, ruleInfo, fullLists));
    }

}
