package aprove.input.Programs.SMTLIB.Namespaces;

import org.antlr.runtime.*;

import aprove.input.Programs.SMTLIB.Terms.IntsTheory.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * The Ints namespace of SMT-LIB
 */
public class IntsNamespace extends SMTNamespace {

    public IntsNamespace(final FormulaFactory<Diophantine> formulaFactory)
            throws RecognitionException {
        this(null, formulaFactory);
    }

    public IntsNamespace(final SMTNamespace parent,
            final FormulaFactory<Diophantine> formulaFactory)
            throws RecognitionException {
        super(parent);
        this.define("-", new MinusFunction(formulaFactory));
        this.define("+", new PlusFunction(formulaFactory));
        this.define("*", new TimesFunction(formulaFactory));
        //this.define("div", null);
        //this.define("mod", null);
        //this.define("abs", null);
        this.define("<=", new LEFunction(formulaFactory));
        this.define("<", new LTFunction(formulaFactory));
        this.define(">=", new GEFunction(formulaFactory));
        this.define(">", new GTFunction(formulaFactory));
    }
}
