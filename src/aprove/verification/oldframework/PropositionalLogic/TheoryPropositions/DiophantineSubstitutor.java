package aprove.verification.oldframework.PropositionalLogic.TheoryPropositions;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;

public class DiophantineSubstitutor implements
        TheoryConverter<Diophantine, Diophantine> {
    private final Map<String, SimplePolynomial> substitution;
    private final FormulaFactory<Diophantine> formulaFactory;

    public DiophantineSubstitutor(
            final Map<String, SimplePolynomial> substitution,
            final FormulaFactory<Diophantine> formulaFactory) {
        this.substitution = substitution;
        this.formulaFactory = formulaFactory;
    }

    @Override
    public Formula<Diophantine> convert(final Diophantine theoryProposition) {
        return this.formulaFactory.buildTheoryAtom(theoryProposition.substitute(this.substitution));
    }

}
