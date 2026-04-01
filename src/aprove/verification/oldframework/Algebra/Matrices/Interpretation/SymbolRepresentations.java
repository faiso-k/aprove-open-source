package aprove.verification.oldframework.Algebra.Matrices.Interpretation;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;

/**
 * This class is a container for all generated coefficient/variable
 * matrices, so they can be accessed quickly.
 *
 * It mainly consists of the following maps:
 * functionSyms: FunctionSymbol |--> Matrix
 *   -- the function Symbols to their associated matrices
 * dPSyms:       FunctionSymbol |--> Matrix
 *   -- the DP Symbols to their associated matrices
 * functionArgSyms: Pair<FunctionSymbol, Integer> |--> Matrix
 *   -- the individual arguments to their associated matrices
 * multifArgSyms: Map<FunctionSymbol, Map<String, Matrix>>
 *   -- the fArgSymbols using multiple vars/exponents.
 * varSyms: Variable |--> Matrix
 *   -- the variables to their corresponding matrices.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class SymbolRepresentations implements CPFAdditional {

    /* These maps are package-scoped. */
    Map<FunctionSymbol, Matrix> functionSyms;
    Map<FunctionSymbol, Matrix> dpSyms;
    Map<FunctionSymbol, Map<Integer, Matrix>> functionArgSyms;
    Map<FunctionSymbol, Map<String, Matrix>> multifArgSyms;
    Map<TRSVariable, Matrix> varSyms;
    Map<String, BigInteger> output;


    // in case we use rational
    int denominator;

    MatrixFactory fact;

    SymbolRepresentations(final MatrixFactory fact) {
        this.functionSyms = new HashMap<FunctionSymbol, Matrix>();
        this.dpSyms = new HashMap<FunctionSymbol, Matrix>();
        this.functionArgSyms = new HashMap<FunctionSymbol, Map<Integer, Matrix>>();
        this.multifArgSyms = new HashMap<FunctionSymbol, Map<String, Matrix>>();
        this.setVarSyms(new HashMap<TRSVariable, Matrix>());
        this.fact = fact;
    }

    public SymbolRepresentations specialize(final Map<String, BigInteger> mapping, final MatrixFactory fact) {
        final SymbolRepresentations result = new SymbolRepresentations(fact);
        result.denominator = this.denominator;
        result.output = mapping;
        for (final Map.Entry<FunctionSymbol, Matrix> e: this.functionSyms.entrySet()) {
            result.functionSyms.put(e.getKey(), e.getValue().specialize(mapping));
        }
        for (final Map.Entry<FunctionSymbol, Matrix> e: this.dpSyms.entrySet()) {
            result.dpSyms.put(e.getKey(), e.getValue().specialize(mapping));
        }
        for (final Map.Entry<TRSVariable, Matrix> e: this.getVarSyms().entrySet()) {
            result.getVarSyms().put(e.getKey(), e.getValue().specialize(mapping));
        }
        for (final Map.Entry<FunctionSymbol, Map<Integer, Matrix>> e: this.functionArgSyms.entrySet()) {
            final Map<Integer, Matrix> converted = new LinkedHashMap<Integer, Matrix> ();
            for (final Map.Entry<Integer, Matrix> s: e.getValue().entrySet()) {
                converted.put(s.getKey(), s.getValue().specialize(mapping));
            }
            result.functionArgSyms.put(e.getKey(), converted);
        }
        for (final Map.Entry<FunctionSymbol, Map<String, Matrix>> e: this.multifArgSyms.entrySet()) {
            final Map<String, Matrix> converted = new LinkedHashMap<String, Matrix> ();
            for (final Map.Entry<String, Matrix> s: e.getValue().entrySet()) {
                converted.put(s.getKey(), s.getValue().specialize(mapping));
            }
            result.multifArgSyms.put(e.getKey(), converted);
        }

        //TODO: Nonlinear Stuff
        return result;
    }


    // TODO: Second-most ugly imaginable...
    public String export(final Export_Util eu) {
        final StringBuilder result = new StringBuilder("Matrix interpretation "+eu.cite(Citation.MATRO)+":\n");

        final boolean rational = this.denominator > 1;

        if (rational) {
            result.append("Matrix interpretation using rational coefficients "
                + eu.cite(Citation.RATPOLO) + ";\n");
        }
        result.append(eu.linebreak() + "Non-tuple symbols: " + eu.linebreak());
        if (this.functionSyms.isEmpty()) {
            result.append (eu.appSpace() + "none" + eu.linebreak());
        }

        for (final Map.Entry<FunctionSymbol, Matrix> e: this.functionSyms.entrySet()) {
            final FunctionSymbol f = e.getKey();
            final List<String> rowEntries = new ArrayList<String>();
            rowEntries.add(this.showF(f, eu));
            if (rational) {
                rowEntries.add(eu.fraction("1",
                    Integer.toString(this.denominator))
                    + eu.multSign());
            }
            rowEntries.add(e.getValue().setAllIndefsToZero().export(eu));
            rowEntries.add("+");
            final Map<Integer, Matrix> ret = this.functionArgSyms.get(f);
            if (ret != null) {
                for (final Map.Entry<Integer, Matrix> s: ret.entrySet()) {
                    if (rational) {
                        rowEntries.add(eu.fraction("1",
                            Integer.toString(this.denominator))
                            + eu.multSign());
                    }
                    rowEntries.add(s.getValue().setAllIndefsToZero().export(eu));
                    rowEntries.add(eu.multSign());
                    rowEntries.add(this.showXi(s.getKey() + 1, eu));
                    rowEntries.add("+");
                    //result.append("M(" + e.getKey().getName() + "{" + s.getKey() + "}) = " + s.getValue().export(eu) + eu.linebreak());
                }
            }
            rowEntries.remove(rowEntries.size()-1);
            result.append(eu.tableStart(rowEntries.size()));
            result.append(eu.tableRow(rowEntries));
            result.append(eu.tableEnd());
            result.append(eu.linebreak());
            //result.append("M(" + e.getKey().getName() + ") = " + e.getValue().export(eu) + eu.linebreak());
            //Map<Integer, Matrix> ret = functionArgSyms.get(e.getKey());
//            if (ret != null) {
//                for (Map.Entry<Integer, Matrix> s: ret.entrySet()) {
//                    result.append("M(" + e.getKey().getName() + "{" + s.getKey() + "}) = " + s.getValue().export(eu) + eu.linebreak());
//                }
//            }
            final Map<String, Matrix> mret = this.multifArgSyms.get(f);
            if (mret != null) {
                for (final Map.Entry<String, Matrix> s: mret.entrySet()) {
                    result.append("M("
                        + e.getKey().getName()
                        + "{"
                        + s.getKey()
                        + "}) = "
                        + s.getValue().setAllIndefsToZero().export(eu)
                        + eu.linebreak());
                }
            }
        }
        result.append("Tuple symbols: " + eu.linebreak());
        for (final Map.Entry<FunctionSymbol, Matrix> e: this.dpSyms.entrySet()) {
            final FunctionSymbol f = e.getKey();
            final List<String> rowEntries = new ArrayList<String>();
            rowEntries.add(this.showF(f, eu));
            if (rational) {
                rowEntries.add(eu.fraction("1",
                    Integer.toString(this.denominator))
                    + eu.multSign());
            }
            rowEntries.add(e.getValue().setAllIndefsToZero().export(eu));
            rowEntries.add("+");
            final Map<Integer, Matrix> ret = this.functionArgSyms.get(f);
            if (ret != null) {
                for (final Map.Entry<Integer, Matrix> s: ret.entrySet()) {
                    if (rational) {
                        rowEntries.add(eu.fraction("1",
                            Integer.toString(this.denominator))
                            + eu.multSign());
                    }
                    rowEntries.add(s.getValue().setAllIndefsToZero().export(eu));
                    rowEntries.add(eu.multSign());
                    rowEntries.add(this.showXi(s.getKey() + 1, eu));
                    rowEntries.add("+");
                }
            }
            rowEntries.remove(rowEntries.size()-1);
            result.append(eu.tableStart(rowEntries.size()));
            result.append(eu.tableRow(rowEntries));
            result.append(eu.tableEnd());
            result.append(eu.linebreak());


//            result.append("M(" + e.getKey().getName() + ") = " + e.getValue().export(eu) + eu.linebreak());
//            Map<Integer, Matrix> ret = functionArgSyms.get(e.getKey());
//            if (ret != null) {
//                for (Map.Entry<Integer, Matrix> s: ret.entrySet()) {
//                    result.append("M(" + e.getKey().getName() + "{" + s.getKey() + "}) = " + s.getValue().export(eu) + eu.linebreak());
//                }
//            }
            final Map<String, Matrix> mret = this.multifArgSyms.get(e.getKey());
            if (mret != null) {
                for (final Map.Entry<String, Matrix> s: mret.entrySet()) {
                    result.append("M("
                        + e.getKey().getName()
                        + "{"
                        + s.getKey()
                        + "}) = "
                        + s.getValue().setAllIndefsToZero().export(eu)
                        + eu.linebreak());
                }
            }
        }

        result.append(eu.newline());
        result.append("Matrix type: ");
        result.append(eu.newline());
        result.append(this.fact.proofAddition(eu, this.output));

        result.append(eu.newline());


        return result.toString();
    }

    /**
     *
     * @param f
     * @param o
     * @return M(f(x_1, ..., x_n))
     */
    private String showF(final FunctionSymbol f, final Export_Util o) {
        final int arity = f.getArity();
        String fString = o.export(f);
        if (arity >= 1) {
            fString += o.export("(x") + o.sub(""+1);
            if (arity > 2) {
                fString += o.export(", ...");
            }
            if (arity >= 2) {
                fString += o.export(", x")+o.sub(""+arity);
            }
            fString += ")";
        }
        final String fToPol = o.bold("M( ")+fString+o.bold(" )")+o.export(" = ");
        return fToPol;
    }

    /**
     *
     * @param i
     * @param o
     * @return x_i
     */
    private String showXi(final int i, final Export_Util o) {
        return o.bold("x" + o.sub(Integer.toString(i)));
    }

    void setVarSyms(final Map<TRSVariable, Matrix> varSyms) {
        this.varSyms = varSyms;
    }

    public Map<TRSVariable, Matrix> getVarSyms() {
        return this.varSyms;
    }

    
    public Map<FunctionSymbol, Matrix> getFuncSyms() {
        return this.functionSyms;
    }
    
    public Map<FunctionSymbol, Map<Integer, Matrix>> getFuncArgSyms() {
        return this.functionArgSyms;
    }
    
    
    /**
     * checks whether a certain function position is active
     * @param f the function symbol
     * @param i the position (counting from 0 onwards)
     * @return false, if it is guaranteed that the interpretation of ti has no impact when interpreting f(t0, ..., t_(n-1));
     *   true, otherwise if the i-th position may be active.
     */
    public boolean isActive(FunctionSymbol f, int i) {
        Map<String,Matrix> multi = this.multifArgSyms.get(f);
        if (multi != null && !multi.isEmpty()) {
            // TODO: do not know the encoding of these maps,
            //   so currently encode safety: true
            return true;
        }
        Map<Integer,Matrix> single = this.functionArgSyms.get(f);
        if (single == null) {
            // we do not know anything about this function symbol
            return true; // true chosen as safety value
        }
        Matrix m = single.get(i);
        return !m.getList().isEmpty();
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {

        int dimension = 0;
        final Map<FunctionSymbol,Matrix> allSyms = new LinkedHashMap<>(this.dpSyms);
        allSyms.putAll(this.functionSyms);

        for (final Matrix m : allSyms.values()) {
            if (dimension < m.getNumRows()) {
                dimension = m.getNumRows();
            }
        }

        final Element delta =
            CPFTag.DELTA.create(
                doc,
            CPFTag.RATIONAL.create(
                doc,
                CPFTag.NUMERATOR.create(doc, 1),
                    CPFTag.DENOMINATOR.create(doc, this.denominator)));

        final Element domain = CPFTag.DOMAIN.create(doc,
            CPFTag.MATRICES.create(doc,
                CPFTag.DIMENSION.create(doc, dimension),
                CPFTag.STRICT_DIMENSION.create(doc, 1),
                CPFTag.DOMAIN.create(doc,
                    CPFTag.RATIONALS.create(doc, delta))));
        final Element matrixInterpretation =
            CPFTag.POLYNOMIAL.create(doc,
                domain,
                CPFTag.DEGREE.create(doc, 1));
        final Element interpretation = CPFTag.INTERPRETATION.create(doc, CPFTag.TYPE.create(doc, matrixInterpretation));

        for (final Map.Entry<FunctionSymbol, Matrix> e : allSyms.entrySet()) {
            final FunctionSymbol fSym = e.getKey();
            final Element interpret =
                CPFTag.INTERPRET.create(doc, fSym.toCPF(doc, xmlMetaData), CPFTag.ARITY.create(doc, fSym.getArity()));

            final Matrix m = e.getValue();

            final Element sum = CPFTag.SUM.create(doc);
            sum.appendChild(CPFTag.POLYNOMIAL.create(
                doc,
                CPFTag.COEFFICIENT.create(
                    doc,
 m.setAllIndefsToZero().toRatCPF(doc, this.denominator, dimension))));
            final Map<Integer, Matrix> ret = this.functionArgSyms.get(fSym);

            if (ret != null) {
                for (final Map.Entry<Integer, Matrix> s : ret.entrySet()) {
                    final Element coeff =
                        CPFTag.POLYNOMIAL.create(
                            doc,
                            CPFTag.COEFFICIENT.create(
                                doc,
                                s.getValue().setAllIndefsToZero().toRatCPF(doc, this.denominator, dimension)));
                    final Element var = CPFTag.POLYNOMIAL.create(doc, CPFTag.VARIABLE.create(doc, (s.getKey() + 1)));

                    sum.appendChild(CPFTag.POLYNOMIAL.create(doc, CPFTag.PRODUCT.create(doc, coeff, var)));
                }
            }
            interpret.appendChild(CPFTag.POLYNOMIAL.create(doc, sum));
            interpretation.appendChild(interpret);
        }

        return CPFTag.ORDERING_CONSTRAINT_PROOF.create(doc, CPFTag.RED_PAIR.create(doc, interpretation));
    }

}

