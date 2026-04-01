package aprove.verification.oldframework.SMT.Solver.SMTInterpol;

import java.io.*;
import java.math.*;
import java.util.*;

import org.apache.log4j.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.*;
import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.logic.Script.*;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.*;

/**
 * Delegates to the SMT solver SMTInterpol within the very same JVM as AProVE.
 * This means only little startup overhead, but it is asymptotically
 * probably not the fastest. Good if your SMT instances are small, but you
 * have many of them. (This is analogous to SAT4J instead of more efficient
 * external solvers like MiniSAT for standard SAT instances.)
 *
 * Similarities of the implementation to Z3IntSolver are not a coincidence.
 *
 * @author fuhs
 */
public class SMTInterpolIntSolver implements SMTSolver {

    /**
     * Magic string from the SMTLIB2 standard.
     */
    private static final String SORT_INT = "Int";

    /**
     * Magic string from the SMTLIB2 standard.
     */
    private static final String SORT_BOOL = "Bool";

    /**
     * TODO docu guess: Used theory.
     */
    @SuppressWarnings("unused")
    private final SMTLIBLogic logic;

    /**
     * Does all the actual work for us, most prominently implemented by SMTInterpol.
     */
    private final Script script;

    /**
     * Aborter.
     */
    private final Abortion abortion;

    /**
     * Fresh names for functions and variables (number).
     */
    private int symbolNumber = 0; // very much not final

    /**
     * Fresh names for functions and variables (prefix).
     */
    private static final String NAME_PREFIX = "v";

    /** Keeps track of all those non-predefined symbols. */
    private ArrayDeque<LinkedHashMap<aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol<?>, String>> state = new ArrayDeque<>();

    /**
     * @param logic - which logic shall we use? (non-null)
     * @param abortion - knows when it's time to wrap up (non-null)
     */
    public SMTInterpolIntSolver(SMTLIBLogic logic, Abortion abortion) {
        this.abortion = abortion;
        this.logic = logic;
        TerminationRequest terminationRequest = new AbortionTerminationRequest(abortion);
        Logger logger = Logger.getRootLogger();
        logger.setLevel(Level.WARN);
        this.script = new SMTInterpol(logger, terminationRequest);
        this.script.setOption(":produce-assignments", true);
        this.script.setOption(":produce-models", true);
        Logics smtInterpolLogic = SMTInterpolIntSolver.toSMTInterpolLogic(logic);
        this.script.setLogic(smtInterpolLogic);
        this.state.push(new LinkedHashMap<aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol<?>, String>());
    }

    /**
     * @param aproveLogic - non-null
     * @return an equivalent representation of AProVE's SMTLIB2 logic
     *  as SMTInterpol's SMTLIB2 logic
     */
    private static Logics toSMTInterpolLogic(SMTLIBLogic aproveLogic) {
        switch (aproveLogic) {
        case AUFLIA :
            return Logics.AUFLIA;
        case AUFLIRA :
            return Logics.AUFLIRA;
        case AUFNIRA :
            return Logics.AUFNIRA;
        case LRA :
            return Logics.LRA;
        case QF_ABV :
            return Logics.QF_ABV;
        case QF_AUFBV :
            return Logics.QF_AUFBV;
        case QF_AUFLIA :
            return Logics.QF_AUFLIA;
        case QF_AX :
            return Logics.QF_AX;
        case QF_BV :
            return Logics.QF_BV;
        case QF_IDL :
            return Logics.QF_IDL;
        case QF_LIA :
            return Logics.QF_LIA;
        case QF_LRA :
            return Logics.QF_LRA;
        case QF_NIA :
            return Logics.QF_NIA;
        case QF_NRA :
            return Logics.QF_NRA;
        case QF_RDL :
            return Logics.QF_RDL;
        case QF_UF :
            return Logics.QF_UF;
        case QF_UFBV :
            return Logics.QF_UFBV;
        case QF_UFIDL :
            return Logics.QF_UFIDL;
        case QF_UFLIA :
            return Logics.QF_UFLIA;
        case QF_UFLRA :
            return Logics.QF_UFLRA;
        case QF_UFNRA :
            return Logics.QF_UFNRA;
        case UFLRA :
            return Logics.UFLRA;
        case UFNIA :
            return Logics.UFNIA;
        default :
            throw new RuntimeException("Hitherto unknown logic " + aproveLogic + '!');
        }
    }

    /**
     * @return the underlying SMTInterpol object
     */
    Script getScript() {
        return this.script;
    }

    static int i;
    @Override
    public void addAssertion(SMTExpression<SBool> formula) {
        this.abortion.checkAbortion();
        ExpressionVisitor<Term> visitor = new BuildTermVisitor(this, true);
        Term expr = formula.accept(visitor);
        this.script.assertTerm(expr);
    }

    @Override
    public YNM checkSAT() {
        this.abortion.checkAbortion();
        LBool s = this.script.checkSat();
        switch (s) {
        case SAT:
            return YNM.YES;
        case UNKNOWN:
            return YNM.MAYBE;
        case UNSAT:
            return YNM.NO;
        default:
            throw new RuntimeException("unhandled satisfiability check result: " + s);
        }
    }

    /**
     * Side effect: Increments the counter for the name suffix.
     * @return a fresh symbol name
     */
    private final String createSymbol() {
        return SMTInterpolIntSolver.NAME_PREFIX+(++this.symbolNumber);
    }


    @Override
    public void declare(aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol<?> sym) {
        this.abortion.checkAbortion();
        LinkedHashMap<aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol<?>, String> top = this.state.getLast();
        if (top.containsKey(sym)) {
            throw new RuntimeException("symbol already declared");
        }
        String declaredName = this.generateFuncOrVar(sym);
        top.put(sym, declaredName);
    }

    /**
     * Side effect: Updates the encapsulated script's function declarations
     * (but not the one of this, which is the caller's responsability).
     *
     * @param sym - non-null
     * @return the name that shall be used for sym
     */
    private String generateFuncOrVar(aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol<?> sym) {
        String name = this.createSymbol();
        de.uni_freiburg.informatik.ultimate.logic.Sort range =
                this.getSMTInterpolSort(sym.getReturnSort());

        aprove.verification.oldframework.SMT.Expressions.Sorts.Sort[] args = sym.getArgumentSorts();
        final int l = args.length;
        de.uni_freiburg.informatik.ultimate.logic.Sort[] domain =
                new de.uni_freiburg.informatik.ultimate.logic.Sort[l];
        for (int i = 0; i < l; ++i) {
            domain[i] = this.getSMTInterpolSort(args[i]);
        }

        this.script.declareFun(name, domain, range);
        return name;
    }

    /**
     * Side effect in case <code>autodeclare</code> is true:
     * Declares <code>sym</sym>.
     *
     * @param sym - non-null
     * @param autodeclare - if hitherto unknown, just declare it?
     * @return a corresponding String for sym
     */
    String getFuncDecl(aprove.verification.oldframework.SMT.Expressions.Symbols.Symbol<?> sym, boolean autodeclare) {
        if (!this.state.getLast().containsKey(sym) && autodeclare) {
            this.declare(sym);
        }
        String decl = this.state.getLast().get(sym);
        if (decl == null) {
            throw new RuntimeException("undeclared symbol: " + sym);
        }
        return decl;
    }

    @Override
    public ArrayList<SMTExpression<SBool>> getUnsatCore() {
        throw new RuntimeException("not implemented yet");
    }

    @Override
    public Boolean getValue(SBool sort, SMTExpression<SBool> exp) {
        throw new NotYetImplementedException();
        /*
        try {
            de.uni_freiburg.informatik.ultimate.logic.Model model = this.script.getModel();
            ExpressionVisitor<Term> visitor = new BuildExprVisitor(this.script, false);
            Term expr = exp.accept(visitor);
            Term b = model.evaluate(expr);
            b.equals(obj);
            script.getValue(terms)
            Z3_lbool z = b.getBoolValue();
            switch (z) {
            case Z3_L_FALSE:
                return false;
            case Z3_L_TRUE:
                return true;
            default:
                throw new RuntimeException("unhandled value: " + z);
            }
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }*/
    }

    @Override
    public BigInteger getValue(SInt sort, SMTExpression<SInt> exp) {
        if (exp instanceof Symbol<?>) {
            Model model = script.getModel();
            String internalName = this.state.getFirst().get(exp);
            Term term = model.evaluate(script.term(internalName));
            if (term instanceof ConstantTerm) {
                Object value = ((ConstantTerm) term).getValue();
                if (value instanceof Rational) {
                    Rational rat = (Rational) value;
                    if (rat.denominator().equals(BigInteger.ONE)) {
                        return rat.numerator();
                    }
                }
            }
        }
        throw new NotYetImplementedException();
        /*
        try {
            com.microsoft.z3.Model model = this.solver.getModel();
            ExpressionVisitor<Expr> visitor = new BuildExprVisitor(this, false);
            Expr expr = exp.accept(visitor);
            IntNum i = (IntNum) model.eval(expr, true);
            return i.getBigInteger();
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }
        */
    }

    @Override
    public ArrayList<Boolean> getValues(SBool sort, Iterable<SMTExpression<SBool>> exps) {
        throw new NotYetImplementedException();/*
        try {
            com.microsoft.z3.Model model = this.solver.getModel();
            ExpressionVisitor<Expr> visitor = new BuildExprVisitor(this, false);
            ArrayList<Boolean> results = new ArrayList<>();
            for (Expression<SBool> exp : exps) {
                BoolExpr r = (BoolExpr) model.eval(exp.accept(visitor), true);
                switch (r.getBoolValue()) {
                case Z3_L_FALSE:
                    results.add(Boolean.FALSE);
                    break;
                case Z3_L_TRUE:
                    results.add(Boolean.TRUE);
                    break;
                default:
                    throw new RuntimeException("unhandled value: " + r.getBoolValue());
                }
            }
            return results;
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }*/
    }

    @Override
    public ArrayList<BigInteger> getValues(SInt sort, Iterable<SMTExpression<SInt>> exps) {
        throw new NotYetImplementedException();
        /*
        try {
            com.microsoft.z3.Model model = this.solver.getModel();
            ExpressionVisitor<Expr> visitor = new BuildExprVisitor(this, false);
            ArrayList<BigInteger> results = new ArrayList<>();
            for (Expression<SInt> exp : exps) {
                IntNum r = (IntNum) model.eval(exp.accept(visitor), true);
                results.add(r.getBigInteger());
            }
            return results;
        } catch (Z3Exception e) {
            throw new RuntimeException(e);
        }*/
    }
/*
    Expr getVariable(Symbol0<?> sym, boolean autodeclare) {
        if (!this.state.getLast().containsKey(sym) && autodeclare) {
            this.declare(sym);
        }
        Expr expr = (Expr) this.state.getLast().get(sym);
        if (expr == null) {
            throw new RuntimeException("undeclared symbol: " + sym);
        }
        return expr;
    }
*/

    /**
     * @param sort - non-null; AProVE's way of representing SMTLIB2 sorts
     * @return SMTInterpol's way of representing <code>sort</code>
     */
    private de.uni_freiburg.informatik.ultimate.logic.Sort getSMTInterpolSort(
        aprove.verification.oldframework.SMT.Expressions.Sorts.Sort sort
    ) {
        final String sortName;
        if (sort instanceof SBool) {
            sortName = SMTInterpolIntSolver.SORT_BOOL;
        } else if (sort instanceof SInt) {
            sortName = SMTInterpolIntSolver.SORT_INT;
        } else {
            throw new RuntimeException("unsupported sort: " + sort);
        }
        de.uni_freiburg.informatik.ultimate.logic.Sort res = this.script.sort(sortName);
        return res;
    }

    @Override
    public void pop() {
        this.script.pop(1);
    }

    @Override
    public void push() {
        this.script.push(1);
    }

    @Override
    public void dispose() throws IOException {
        this.script.exit();
    }

    public void reset() {
        this.script.reset();
        this.state.clear();
        this.state.push(new LinkedHashMap<>());
        this.symbolNumber = 0;
        this.script.setLogic(SMTInterpolIntSolver.toSMTInterpolLogic(logic));
    }

}
