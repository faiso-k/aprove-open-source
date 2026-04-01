package aprove.verification.oldframework.IntTRS.PoloRedPair;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Represents a polynomial interpretation.
 * @author Matthias Hoelzel
 */
public final class PolynomialInterpretation {
    /**
     * Maps a function symbol f to a pair (list, poly), where [list] stores the
     * corresponding variables.
     */
    private final Map<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>> pol;

    /**
     * docu guess: Used when applying the interpretation to create fresh variables.
     */
    private final FreshNameGenerator ng;

    /**
     * Constructor
     * @param mapping maps function symbol to a pair (list of variables,
     * polynomial)
     */
    private PolynomialInterpretation(
        final Map<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>> mapping,
        final FreshNameGenerator gen)
    {
        this.pol = mapping;
        this.ng = gen;
    }

    /**
     * Creates a polynomial interpretation.
     * @param mapping maps function symbol to a pair (string-list, polynomial)
     * @param a name generator
     * @return a valid polynomial interpretation
     */
    public static PolynomialInterpretation create(
        final Map<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>> mapping,
        final FreshNameGenerator gen)
    {
        if (Globals.DEBUG_MATTHIAS) {
            // Check whether or not mapping is valid. If not: raise an assertion failure.
            if (mapping == null) {
                assert false;
                return null;
            }
            for (final Entry<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>> entry : mapping.entrySet()) {
                final int arity = entry.getKey().getArity();
                final Pair<ArrayList<String>, VarPolynomial> pair = entry.getValue();
                if (pair == null) {
                    assert false;
                    return null;
                }

                final ArrayList<String> variables = pair.getKey();
                final VarPolynomial poly = pair.getValue();

                if (variables == null || variables.size() != arity || poly == null) {
                    assert false;
                    return null;
                }
            }
        }
        return new PolynomialInterpretation(mapping, gen);
    }

    /**
     * Applies this interpretation to an int-based function application.
     * That mean, that
     * f(t_1, .., t_n) (where t_i are int-terms)
     * will be transformed into
     * pol[f](t_1, .._t_n)
     *
     * <p>Note that this function is not referentially transparent, since it
     * uses the local fresh name generator to instantiate certain terms to fresh variables.</p>
     *
     * @param func a int-based function application
     * @return a VarPolynomial
     */
    public VarPolynomial apply(final TRSFunctionApplication func) {
        if (func == null) {
            if (Globals.DEBUG_MATTHIAS) {
                assert false : "null cannot be interpreted!";
            }
            return null;
        }

        final FunctionSymbol sym = func.getRootSymbol();
        final int arity = sym.getArity();
        final Pair<ArrayList<String>, VarPolynomial> interpretationPair = this.pol.get(sym);
        if (interpretationPair == null) {
            if (Globals.DEBUG_MATTHIAS) {
                assert false : "PolynomialInterpretation.apply(): Cannot interpret \"" + sym + "\"!";
            }
            return null;
        }

        final ArrayList<String> variables = interpretationPair.getKey();
        final VarPolynomial scheme = interpretationPair.getValue();
        final Map<String, VarPolynomial> sigma = new LinkedHashMap<String, VarPolynomial>(arity);
        for (int i = 0; i < arity; i++) {
            sigma.put(variables.get(i), ToolBox.intTermToPolynomial(func.getArgument(i), this.ng));
        }

        return scheme.substituteVariables(sigma);
    }

    /**
     * Specializes [this] by replacing indefinite coefficient by values. Please
     * note, that [this] will be changed!
     * @param substitution specializes this interpretation.
     */
    public void specialize(final Map<String, BigInteger> substitution) {
        for (final Pair<ArrayList<String>, VarPolynomial> pair : this.pol.values()) {
            pair.setValue(pair.getValue().specialize(substitution));
        }
    }

    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder("PolynomialInterpretation:\n");
        for (final Entry<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>> entry : this.pol.entrySet()) {
            final FunctionSymbol fs = entry.getKey();
            final Pair<ArrayList<String>, VarPolynomial> pair = entry.getValue();
            final ArrayList<String> variableNames = pair.getKey();
            final VarPolynomial interpretation = pair.getValue();
            final ArrayList<TRSVariable> variables = new ArrayList<TRSVariable>(variableNames.size());
            for (final String name : variableNames) {
                variables.add(TRSTerm.createVariable(name));
            }
            result.append("[ ");
            result.append(TRSTerm.createFunctionApplication(fs, variables).toString());
            result.append(" ]_pol = ");
            result.append(interpretation.toString());
            result.append("\n");
        }
        return result.toString();
    }

    /**
     * Export the interpretation.
     * @param eu export helper
     * @return string
     */
    public String export(final Export_Util eu) {
        final StringBuilder builder = new StringBuilder();

        for (final Entry<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>> entry : this.pol.entrySet()) {
            final FunctionSymbol fs = entry.getKey();
            final Pair<ArrayList<String>, VarPolynomial> pair = entry.getValue();
            final ArrayList<String> variableNames = pair.getKey();
            final VarPolynomial interpretation = pair.getValue();
            final ArrayList<TRSVariable> variables = new ArrayList<TRSVariable>(variableNames.size());
            for (final String name : variableNames) {
                variables.add(TRSTerm.createVariable(name));
            }
            builder.append(eu.escape("["));
            builder.append(TRSTerm.createFunctionApplication(fs, variables).export(eu));
            builder.append(eu.escape("] = "));
            builder.append(interpretation.export(eu));
            builder.append(eu.linebreak());
        }

        return builder.toString();
    }
    
    public Element toCPF(final Document doc, XMLMetaData xmlMetaData) {
        Element rfs = CPFTag.LTS_RANKING_FUNCTIONS.create(doc);        
        for (final Entry<FunctionSymbol, Pair<ArrayList<String>, VarPolynomial>> entry : this.pol.entrySet()) {
            FunctionSymbol f = entry.getKey();            
            List<String> vars = entry.getValue().x;
            List<String> cpfVars = xmlMetaData.getVarsForFS(f);
            VarPolynomial expr = entry.getValue().y;
            Map<String, String> map = new HashMap<>();
            Iterator<String> cpfIter = cpfVars.iterator();
            for (String v : vars) {
                String x = cpfIter.next();
                map.put(v,  x);
            }
            Element loc = CPFTag.LTS_LOCATION.create(doc, CPFTag.LTS_LOCATION_DUP.create(doc, f.getName()));
            Element exp = CPFTag.LTS_EXPRESSION.create(doc, expr.toLtsCPF(doc, map));            
            Element rf = CPFTag.LTS_RANKING_FUNCTION.create(doc, loc, exp);
            rfs.appendChild(rf);
        }
        return rfs;
    }    
    
}
