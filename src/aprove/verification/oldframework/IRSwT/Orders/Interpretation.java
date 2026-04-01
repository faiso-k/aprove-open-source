package aprove.verification.oldframework.IRSwT.Orders;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Class for representing term interpretations.
 * @author Matthias Hoelzel
 * @param <Domain> Probably integers or rationals.
 */
public class Interpretation<Domain extends Exportable> {
    /**
     * Maps a symbol f to a template term a list of variables (x_1, ..., x_n).
     */
    LinkedHashMap<FunctionSymbol, ArrayList<String>> templates;

    /**
     * Maps the template terms f(x_1, ..., x_n) to its interpretation.
     */
    LinkedHashMap<FunctionSymbol, VarPolynomial> interpretations;

    /**
     * Collects the instantiations.
     */
    LinkedHashMap<String, Domain> instantiation;

    /**
     * Set of coefficients.
     */
    LinkedHashSet<String> coefficients;

    /**
     * Create a interpretation template for a linear interpretation.
     * @param symbols set of non-predefined function symbols
     * @param fng some name generator
     */
    public Interpretation(final Collection<FunctionSymbol> symbols, final FreshNameGenerator fng) {
        this.templates = new LinkedHashMap<>();
        this.instantiation = new LinkedHashMap<>();
        this.interpretations = new LinkedHashMap<>();
        this.coefficients = new LinkedHashSet<>();

        for (final FunctionSymbol symbol : symbols) {
            final String rootCoefficient = fng.getFreshName("c", false);
            this.coefficients.add(rootCoefficient);
            VarPolynomial poly = VarPolynomial.createCoefficient(rootCoefficient);

            final ArrayList<String> variables = new ArrayList<>(symbol.getArity());

            for (int i = 0; i < symbol.getArity(); i++) {
                final String newVariable = fng.getFreshName("x", false);
                final String newCoefficient = fng.getFreshName("c", false);
                this.coefficients.add(newCoefficient);

                variables.add(newVariable);
                poly =
                    poly.plus(VarPolynomial.createCoefficient(newCoefficient).times(
                        VarPolynomial.createVariable(newVariable)));
            }

            this.templates.put(symbol, variables);
            this.interpretations.put(symbol, poly);
        }
    }

    /**
     * Getter for the interpretation polynomials.
     * @param s some symbol
     * @return a polynomial without any instantiations
     */
    public VarPolynomial getInterpretationPolynomial(final FunctionSymbol s) {
        return this.interpretations.get(s);
    }

    /**
     * Returns the template variable used for this interpretation!
     * @param s some symbol
     * @param position with argument do you want?
     * @return string
     */
    public String getTemplateVariable(final FunctionSymbol s, final int position) {
        final ArrayList<String> list = this.templates.get(s);
        if (list == null) {
            return null;
        } else {
            return list.get(position);
        }
    }

    /**
     * Instantiates some coefficients.
     * @param instantiationMap map from variables (strings) to the domain
     */
    public void instantiateCoefficients(final Map<String, Domain> instantiationMap) {
        this.instantiation.putAll(instantiationMap);
    }

    /**
     * Instantiates only one coefficient.
     * @param t some term
     * @param v some value from the domain
     */
    public void instantiateCoefficient(final String t, final Domain v) {
        this.instantiation.put(t, v);
    }

    /**
     * Applies this interpretation to a term and returns a polynomial.
     * However, it does not perform the instantiations, because they might
     * belong to some strange domain.
     * @param t some term
     * @param fng some name generator
     * @return some polynomial
     */
    public VarPolynomial applyInterpretation(final TRSTerm t, final FreshNameGenerator fng) {
        if (t instanceof TRSFunctionApplication) {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (IDPPredefinedMap.DEFAULT_MAP.isPredefined(sym)) {
                return ToolBox.intTermToPolynomial(t, fng);
            } else if (this.templates.containsKey(sym)) {
                final ArrayList<String> templateVariables = this.templates.get(sym);
                final VarPolynomial templatePoly = this.interpretations.get(sym);
                final ImmutableList<TRSTerm> arguments = func.getArguments();
                final LinkedHashMap<String, VarPolynomial> substitution = new LinkedHashMap<>();
                for (int p = 0; p < sym.getArity(); p++) {
                    substitution.put(templateVariables.get(p), this.applyInterpretation(arguments.get(p), fng));
                }
                return templatePoly.substituteVariables(substitution);
            } else {
                assert false : "Default?!";
            }
        } else if (t instanceof TRSVariable) {
            final TRSVariable v = (TRSVariable) t;
            return VarPolynomial.createVariable(v.getName());
        } else {
            assert false : "Default?!";
        }
        return null;
    }

    /**
     * Exports this interpretation.
     * @param eu some export helper
     * @param sb some string builder
     */
    public void export(final Export_Util eu, final StringBuilder sb) {
        for (final Entry<FunctionSymbol, VarPolynomial> e : this.interpretations.entrySet()) {
            sb.append(eu.escape("["));
            final FunctionSymbol sym = e.getKey();
            final VarPolynomial vp = e.getValue();
            sb.append(sym.export(eu));
            sb.append(eu.escape("("));

            final Iterator<String> varIterator = this.templates.get(sym).iterator();
            while (varIterator.hasNext()) {
                final String nextVar = varIterator.next();
                sb.append(eu.escape(nextVar));
                if (varIterator.hasNext()) {
                    sb.append(eu.escape(", "));
                }
            }

            sb.append(eu.escape(")] "));
            sb.append(eu.eqSign());
            sb.append(eu.escape(" "));
            sb.append(vp.export(eu, this.getRepresentations(eu)));

            sb.append(eu.linebreak());
        }
    }

    /**
     * Exports the instantiation map.
     * @param eu some export helper
     * @return maps strings to strings
     */
    private Map<String, String> getRepresentations(final Export_Util eu) {
        final LinkedHashMap<String, String> result = new LinkedHashMap<>();
        for (final Entry<String, Domain> e : this.instantiation.entrySet()) {
            final String s = e.getKey();
            final Domain d = e.getValue();
            result.put(s, d.export(eu));
        }
        return result;
    }

    /**
     * Exports this interpretation.
     * @param eu some export helper
     * @return string
     */
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();
        this.export(eu, sb);
        return sb.toString();
    }
}
