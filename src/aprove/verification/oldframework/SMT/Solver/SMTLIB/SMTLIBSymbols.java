package aprove.verification.oldframework.SMT.Solver.SMTLIB;

import aprove.verification.oldframework.SMT.Solver.SMTLIB.SExp.*;

public class SMTLIBSymbols {

    public static final SExpSymbol And = new SExpSymbol("and");
    public static final SExpSymbol Assert = new SExpSymbol("assert");
    public static final SExpSymbol Bool = new SExpSymbol("Bool");
    public static final SExpSymbol declareFun = new SExpSymbol("declare-fun");
    public static final SExpSymbol defineFun = new SExpSymbol("define-fun");
    public static final SExpSymbol Distinct = new SExpSymbol("distinct");
    public static final SExpSymbol Equivalent = new SExpSymbol("=");
    public static final SExpSymbol Exists = new SExpSymbol("exists");
    public static final SExpSymbol False = new SExpSymbol("false");
    public static final SExpSymbol Forall = new SExpSymbol("forall");
    public static final SExpSymbol GetValue = new SExpSymbol("get-value");
    public static final SExpSymbol Implies = new SExpSymbol("=>");
    public static final SExpSymbol Int = new SExpSymbol("Int");
    public static final SExpSymbol IntsAbs = new SExpSymbol("abs");
    public static final SExpSymbol IntsAdd = new SExpSymbol("+");
    public static final SExpSymbol IntsDiv = new SExpSymbol("div");
    public static final SExpSymbol IntsGreater = new SExpSymbol(">");
    public static final SExpSymbol IntsGreaterEqual = new SExpSymbol(">=");
    public static final SExpSymbol IntsLess = new SExpSymbol("<");
    public static final SExpSymbol IntsLessEqual = new SExpSymbol("<=");
    public static final SExpSymbol IntsMod = new SExpSymbol("mod");
    public static final SExpSymbol IntsNegate = new SExpSymbol("-");
    public static final SExpSymbol IntsSubtract = new SExpSymbol("-");
    public static final SExpSymbol IntsTimes = new SExpSymbol("*");
    public static final SExpSymbol ITE = new SExpSymbol("ite");
    public static final SExpSymbol Not = new SExpSymbol("not");
    public static final SExpSymbol Or = new SExpSymbol("or");
    public static final SExpSymbol Sat = new SExpSymbol("sat");
    public static final SExpSymbol SetLogic = new SExpSymbol("set-logic");
    public static final SExpSymbol SetOption = new SExpSymbol("set-option");
    public static final SExpSymbol True = new SExpSymbol("true");
    public static final SExpSymbol Unknown = new SExpSymbol("unknown");
    public static final SExpSymbol Unsat = new SExpSymbol("unsat");
    public static final SExpSymbol Xor = new SExpSymbol("xor");

}
