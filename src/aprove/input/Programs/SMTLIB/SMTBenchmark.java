package aprove.input.Programs.SMTLIB;

import java.util.*;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Exceptions.*;
import aprove.input.Programs.SMTLIB.Namespaces.*;
import aprove.input.Programs.SMTLIB.Sorts.*;
import aprove.input.Programs.SMTLIB.Terms.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Represents a SMT-LIB benchmark.
 */
public class SMTBenchmark {
    public static enum Status {
        UNKNOWN, SAT, UNSAT;

        @Override
        public String toString() {
            return this.name().toLowerCase();
        }
    }

    private String logic = null;
    private String category;
    private Status status = null;

    private final Set<String> supportedLogic = new HashSet<String>();
    private Formula<Diophantine> assertionStack = null;
    private final SMTNamespace namespace;
    private final List<String> letVars = new ArrayList<String>();

    private final FormulaFactory<Diophantine> formulaFactory =
        new FullSharingFlatteningFactory<Diophantine>();

    private boolean checkSat = false;

    private SMTBenchmark() throws RecognitionException {
        this.namespace =
            new SMTNamespace(new IntsNamespace(new CoreNamespace(
                this.formulaFactory), this.formulaFactory));
        this.supportedLogic.add("QF_NIA");
    }

    /**
     * Creates a new smt-benchmark wrapper class which the SMTBenchmark.g
     * grammar is using to parse smt-benchmarks to AProVe problems
     * @return new SMTBenchmark
     * @throws RecognitionException
     */
    public static SMTBenchmark create() throws RecognitionException {
        return new SMTBenchmark();
    }

    public Formula<Diophantine> getAssertions() {
        return this.assertionStack;
    }

    public SMTNamespace getNamespace() {
        return this.namespace;
    }

    public List<String> getLetVariables() {
        return this.letVars;
    }

    public void addLetVariable(final String e) {
        this.letVars.add(e);
    }

    public FormulaFactory<Diophantine> getFormulaFactory() {
        return this.formulaFactory;
    }

    public Set<String> getVariables() {
        return this.namespace.getIdentifiers(true);
    }

    public void setLogic(final String logic) throws RecognitionException {
        if (this.logic != null) {
            throw new MultipleCallsException("set-logic");
        }

        this.logic = logic.toUpperCase();

        if (! this.isSupportedLogic()) {
            throw new UnsupportedException("The logic '" + logic
                + "' is not supported.");
        }
    }

    public String getLogic() {
        return this.logic;
    }

    public boolean isSupportedLogic() {
        return this.supportedLogic.contains(this.logic);
    }


    public void setInfo(final String flag, final String value)
            throws RecognitionException {
        if (flag.compareTo(":status") == 0) {
            this.setStatus(value);
        } else if (flag.compareTo(":category") == 0) {
            this.setCategory(value.substring(1, value.length() - 1));
        }
    }


    public void setStatus(final String status) throws RecognitionException {
        this.setStatus(this.statusFromString(status));
    }

    private Status statusFromString(String status) {
        if (status == null) {
            return Status.UNKNOWN;
        } else if (status.compareToIgnoreCase("sat") == 0) {
            return Status.SAT;
        } else if (status.compareToIgnoreCase("unsat") == 0) {
            return Status.UNSAT;
        } else {
            return Status.UNKNOWN;
        }
    }

    public void setStatus(final Status status) throws RecognitionException {
        if (this.status != null) {
            throw new MultipleCallsException("set-status");
        }

        this.status = status;
    }

    public Status getStatus() {
        return this.status;
    }


    public void setCategory(final String category) {
        this.category = category;
    }

    public String getCategory() {
        return this.category;
    }

    public boolean doCheckSat() {
        return this.checkSat;
    }


    /**
     * Puts the symbol into the declaration namespace and defines it as a
     * Varibale. NOTICE! This is only a espacially adapted function for QF_NIA
     * benchmarks wich only contains variables of Int or Bool.
     * @param symbol The symbol
     * @param sort The sort of the symbol
     * @throws RecognitionException
     */
    public void declareFun(final String symbol, final NativeSort sort)
            throws RecognitionException {
        if (this.namespace.isDeclared(symbol)) {
            throw new MultipleCallsException("declare-fun");
        }

        this.namespace.declare(symbol, sort);

        if (SortBool.SORTBOOL.equalsWith(sort)) {

            this.namespace.define(symbol, new DiophantineFormulaWrapper(
                new Variable<Diophantine>(), this.formulaFactory));
        } else if (SortInt.SORTINT.equalsWith(sort)) {
            this.namespace.define(symbol, new SimplePolynomialWrapper(
                SimplePolynomial.create(symbol), this.formulaFactory));
        } else {
            throw new UnsupportedSortException("declare-fun");
        }
    }

    /**
     * Puts a new assertion to the assertion stack.
     * @param f The new assertion as a formula
     */
    public void assertFormula(final Formula<Diophantine> f) {
        if (this.assertionStack == null) {
            this.assertionStack = f;
        } else if (f != null) {
            this.assertionStack =
                this.formulaFactory.buildAnd(this.assertionStack, f);
        }
    }

    /**
     * Try to solve the diophantine constraints. Stores the result in attribute
     * result.
     * @throws RecognitionException
     */
    public void checkSat() throws RecognitionException {
        if (this.checkSat) {
            throw new MultipleCallsException("check-sat");
        } else {
            this.checkSat = true;
        }

        if (this.assertionStack == null) {
            throw new NoAssertionsException();
        }

        //System.err.println(this.assertionStack);
    }
}
