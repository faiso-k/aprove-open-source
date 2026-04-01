package aprove.input.Programs.SMTLIB.Namespaces;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Terms.CoreTheory.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * The Core namespace of SMT-LIB
 */
public class CoreNamespace extends SMTNamespace {

    public CoreNamespace(final FormulaFactory<Diophantine> formulaFactory)
            throws RecognitionException {
        this(null, formulaFactory);
    }

    public CoreNamespace(final SMTNamespace parent,
            final FormulaFactory<Diophantine> formulaFactory)
            throws RecognitionException {
        super(parent);
        this.define("true", new TrueConstant(formulaFactory));
        this.define("false", new FalseConstant(formulaFactory));

        this.define("not", new NotFunction(formulaFactory));
        this.define("=>", new ImpliesFunction(formulaFactory));
        this.define("and", new AndFunction(formulaFactory));
        this.define("or", new OrFunction(formulaFactory));
        this.define("xor", new XorFunction(formulaFactory));

        this.define("=", new EqualsFunction(formulaFactory));
        this.define("ite", new ITEFunction(formulaFactory));
    }
}
