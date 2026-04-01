package aprove.verification.oldframework.IntTRS.CaseAnalysis;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Represents a condition over terms with one (outermost) undefined symbol.
 * @author Matthias Hoelzel
 */
public class GEZeroCondition {
    /** Maps function symbols to template interpretations. */
    private final ImmutableLinkedHashMap<FunctionSymbol, Pair<TRSFunctionApplication, VarPolynomial>> geZeroTerms;

    /**
     * Constructor!
     * @param terms the interpretation templates
     */
    public GEZeroCondition(final LinkedHashMap<FunctionSymbol, Pair<TRSFunctionApplication, VarPolynomial>> terms) {
        this.geZeroTerms = ImmutableCreator.create(terms);
        this.checkSanity();
    }

    /**
     * Constructor!
     * @param terms the interpretation templates
     */
    public GEZeroCondition(final ImmutableLinkedHashMap<FunctionSymbol, Pair<TRSFunctionApplication, VarPolynomial>> terms)
    {
        this.geZeroTerms = terms;
        this.checkSanity();
    }

    /**
     * Checks whether or not the interpretation is valid!
     * Raises asserts, when its not. [This is just for debugging purposes!]
     */
    private void checkSanity() {
        for (final Entry<FunctionSymbol, Pair<TRSFunctionApplication, VarPolynomial>> e : this.geZeroTerms.entrySet()) {
            assert e.getKey() != null && e.getValue() != null : "Null!";
            assert e.getKey().equals(e.getValue().x.getRootSymbol()) : "Symbols do not match!";
            assert e.getValue().x.isLinear() : "Non-linear terms are not allowed!";

            final Set<TRSVariable> variables = e.getValue().x.getVariables();
            for (final String var : e.getValue().y.getVariables()) {
                assert variables.contains(TRSTerm.createVariable(var)) : "Weird variable detected: "
                    + var
                    + " not contained in "
                    + variables;
            }
        }
    }

    /**
     * Getter for the interpretation templates.
     * @return maps function symbols to the interpretations
     */
    public ImmutableLinkedHashMap<FunctionSymbol, Pair<TRSFunctionApplication, VarPolynomial>> getGeZeroTerms() {
        return this.geZeroTerms;
    }

    /**
     * Builds the formula expressing that funcy satisfies the given condition.
     * @param funcy some function application
     * @return some precious SMT formula
     */
    public VarPolynomial buildCorrespondingPolynomial(final TRSFunctionApplication funcy, final FreshNameGenerator ng) {
        final Pair<TRSFunctionApplication, VarPolynomial> p = this.getGeZeroTerms().get(funcy.getRootSymbol());
        final TRSFunctionApplication schema = p.x;
        final TRSSubstitution matcher = schema.getMatcher(funcy);
        final Set<TRSVariable> variables = schema.getVariables();

        final LinkedHashMap<String, VarPolynomial> vpSubstitution = new LinkedHashMap<>();
        for (final TRSVariable v : variables) {
            vpSubstitution.put(v.getName(), ToolBox.intTermToPolynomial(v.applySubstitution(matcher), ng));
        }
        final VarPolynomial toBeGeZero = p.y.substituteVariables(vpSubstitution);

        return toBeGeZero;
    }

    /**
     * Builds the formula expressing that funcy satisfies the given condition.
     * @param funcy some function application
     * @return some precious SMT formula
     */
    public Formula<SMTLIBTheoryAtom> buildCorrespondingGEConstraint(
        final TRSFunctionApplication funcy,
        final FreshNameGenerator ng,
        final FormulaFactory<SMTLIBTheoryAtom> factory)
    {
        return factory.buildTheoryAtom(SMTLIBIntGE.create(
            this.buildCorrespondingPolynomial(funcy, ng).toSMTLIB(),
            SMTLIBIntConstant.create(BigInteger.ZERO)));
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (final Pair<TRSFunctionApplication, VarPolynomial> v : this.geZeroTerms.values()) {
            if (!first) {
                sb.append(", ");
            }
            first = false;
            sb.append(v.x.toString());
            sb.append(": ");
            sb.append(v.y.toString());
        }
        return sb.toString();
    }
}
