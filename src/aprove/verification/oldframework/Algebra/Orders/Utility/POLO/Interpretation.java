package aprove.verification.oldframework.Algebra.Orders.Utility.POLO;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Verifier.*;

/**
 * Polynomial interepration of ground terms over a certain signature.
 *
 * @author Andreas Capellmann
 * @version $Id$
 */
public class Interpretation extends HashMap<SyntacticFunctionSymbol, Polynomial> implements Exportable {

    private static Logger log =
        Logger.getLogger("aprove.verification.oldframework.Algebra.Orders.Utility.POLO.Interpretation");

    public static final int INDIVIDUAL = -2;
    public static final int LINEAR = 1;
    public static final int SIMPLE = -1;
    public static final int SIMPLE_MIXED = 0;
    public static final String VARIABLE_PREFIX = "x_";

    public VariableFactory coefficientFactory;
    /* guess (thiemann):
     * coefficients are a mapping from f's to Poly-Arrays such that
     * if Pol(f) = a+bx + cxy+dy+ez then
     * map(f) = [b+c,c+d,e]
     * so, in the i-th array-position is a polynomial representing which coefficients have
     * impact on the i-th variable of f(x,y,...)
     */
    public Map<SyntacticFunctionSymbol, Polynomial[]> coefficients;

    private Interpretation(VariableFactory factory) {
        this.coefficientFactory = factory;
        this.coefficients = new HashMap<SyntacticFunctionSymbol, Polynomial[]>();
    }

    /**
     * returns constraints ensuring strong monotonicity
     * of the given interpretation (assuming that all a_i's
     * mentioned below are at least 0):
     *
     * for each function symbol f with interpretation
     * Pol(f(x_1..x_n)) = Sum a_ix_1^p_1..x_n^p^n
     * there will be created n constraints, namely
     * a_i > 0 where a_i corresponds to the monom x_i
     */
    public Map<PolyConstraint, Set<String>> getStrongMonotonicityConstraints() {
        Map<PolyConstraint, Set<String>> constraints = new LinkedHashMap<PolyConstraint, Set<String>>();
        Set<String> noVars = new LinkedHashSet<String>();
        for (Entry<SyntacticFunctionSymbol, Polynomial> e : this.entrySet()) {
            int arity = e.getKey().getArity();

            // construct variables
            Set<String> xs = new LinkedHashSet<String>();
            for (int i=1; i<= arity; i++) {
                xs.add(Interpretation.VARIABLE_PREFIX + i);
            }

            // iterate over all variables/positions
            for (String x : xs) {
                Polynomial p = e.getValue().getCoefficientForVariable(x, xs);
                PolyConstraint c = PolyConstraint.create(p, AbstractConstraint.GR);
                constraints.put(c, noVars);
            }
        }
        return constraints;
    }

    public static Interpretation create(Constraints constraints, int degree) {
        Interpretation interpretation =
            new Interpretation(CoefficientFactory.create(constraints.getVariableNames()));

        for (Iterator iter = constraints.iterator(); iter.hasNext();) {
            interpretation.extend((Constraint) iter.next(), degree);
        }

        return interpretation;
    }

    public static Interpretation create(VariableFactory factory) {
        return new Interpretation(factory);
    }



    public VariableFactory getCoefficientFactory() {
        return this.coefficientFactory;
    }

    public void extend(Constraint constraint, int degree) {
        for (Iterator iter = constraint.getFunctionSymbols().iterator(); iter.hasNext();) {
            this.extend((SyntacticFunctionSymbol) iter.next(), degree);
        }
    }

    public void extend(SyntacticFunctionSymbol symbol, int degree) {
        if (this.keySet().contains(symbol)) {
            return;
        }

        this.put(symbol, this.getPolynomialFromFunction(symbol, degree));
    }

    public void extend(SyntacticFunctionSymbol symbol, Polynomial polynomial) {
        if (this.keySet().contains(symbol)) {
            return;
        }

        this.put(symbol, polynomial);

        // calculate the coefficients of the symbol's arguments
        Polynomial[] coeffs = new Polynomial[symbol.getArity()];
        Arrays.fill(coeffs, Polynomial.ZERO);

        // build the set of argument names
        Set<String> arguments = new LinkedHashSet<String>();
        for (int i = 0; i < symbol.getArity(); ++i) {
            String variable = Interpretation.VARIABLE_PREFIX + (i + 1);
            if (polynomial.containsVariable(variable)) {
                arguments.add(variable);
            }
        }

        // calculate the coefficients argument by argument
        for (int i = 0; i < symbol.getArity(); ++i) {
            String variable = Interpretation.VARIABLE_PREFIX + (i + 1);

            for (Monomial m : polynomial) {

                if (m.containsVariable(variable)) {
                    SortedMap<String, Integer> exponents = new TreeMap<String, Integer>();
                    for (String var : m.exponents.keySet()) {
                        if (!arguments.contains(var)) {
                            exponents.put(var, Integer.valueOf(1));
                        }
                    }

                    if (coeffs[i] == null) {
                        coeffs[i] = Polynomial.create(Monomial.create(1, exponents));
                    } else {
                        coeffs[i] = coeffs[i].plus(Polynomial.create(Monomial.create(1, exponents)));
                    }
                }
            }
        }

        this.coefficients.put(symbol, coeffs);
    }

    /**
     * Calculates the first partial derivation of each variable for all symbols that are part of this
     * interpretation. The derivations then form new polynomial constraints which can be strict or
     * non-strict according to the given parameter.
     *
     * Deprecated, use getStrongMonotonicityConstraints
     *
     * @param strict decides wheter the produced constraint should be strict
     * @return the produced constraints mapped to the allquantified variables occuring in itself
     * @deprecated
     */
    @Deprecated
    public Map getDerivations(boolean strict) {
        Map<PolyConstraint, Set<String>> constraints = new LinkedHashMap<PolyConstraint, Set<String>>();

        for (Entry<SyntacticFunctionSymbol,Polynomial> entry : this.entrySet()) {

            SyntacticFunctionSymbol function = entry.getKey();
            Polynomial polynomial = entry.getValue();

            // calculate arguments of the current function
            Set<String> variables = new LinkedHashSet<String>();
            for (int i = 0; i < function.getArity(); ++i) {
                variables.add(Interpretation.VARIABLE_PREFIX + (i + 1));
            }

            // calculate derivations of interpretational polynomials
            for (String variable : variables) {
                Polynomial derivation = polynomial.partiallyDerive(variable);

                int type = (strict) ? AbstractConstraint.GR : AbstractConstraint.GE;
                PolyConstraint constraint = PolyConstraint.create(derivation, type);

                Set<String> remainingVariables = new LinkedHashSet<String>(variables);
                remainingVariables.retainAll(derivation.getVariables());

                constraints.put(constraint, remainingVariables);
            }
        }

        return constraints;
    }

    /**
     * Calculates the polynomial interpretation of a term constraint based on the present
     * interpretation of the signature.
     *
     * @param constraint the term constraint to convert
     * @param variables variables accumulator
     * @return the polynomial interpretation of the given term constraint
     */
    public PolyConstraint getPolynomialConstraint(Constraint constraint, Set<String> variables) {
        Polynomial polynomial = GeneratePolynomialVisitor.apply(constraint.getLeft(), this, variables);
        polynomial =
            polynomial.minus(GeneratePolynomialVisitor.apply(constraint.getRight(), this, variables));

        return PolyConstraint.create(polynomial, constraint.getType());
    }

    public PolyConstraint getPolynomialConstraint(Rule rule, int type, Set<String> variables) {
        Polynomial left =
            GeneratePolynomialVisitor.apply(rule.getLeft(), this, variables);
        Polynomial right =
            GeneratePolynomialVisitor.apply(rule.getRight(), this, variables);

        Polynomial polynomial = left.minus(right);

        variables.retainAll(polynomial.getVariables());

        return  PolyConstraint.create(polynomial, type);
    }

    public PolyConstraint getPolynomialConstraint(TRSEquation equation, int type, Set<String> variables) {
        Polynomial left = GeneratePolynomialVisitor.apply(equation.getOneSide(), this, variables);
        Polynomial right = GeneratePolynomialVisitor.apply(equation.getOtherSide(), this, variables);

        Polynomial polynomial = left.minus(right);

        variables.retainAll(polynomial.getVariables());

        return  PolyConstraint.create(polynomial, type);
    }

    /**
     * Calculates the polynomial interpretation of a set of term constraints based on the present
     * interpretation of the signature.
     *
     * @param constraints set of term constraints to convert
     * @return the polynomial interpretation of the given term constraints mapped to the occuring
     *   allquantified variables
     */
    public Map<PolyConstraint, Set<String>> getPolynomialConstraints(Set<Constraint> constraints, Abortion aborter) throws AbortionException {
        Map<PolyConstraint, Set<String>> cs = new LinkedHashMap<PolyConstraint, Set<String>>();
        Interpretation.log.log(Level.CONFIG, "Creating polynomial constraints for "+constraints.size()+" term constraints...\n");
        for (Constraint constraint : constraints) {
            aborter.checkAbortion();
            Interpretation.log.log(Level.FINE, "Processing constraint {0}.\n", constraint);
            Set<String> variables = new LinkedHashSet<String>();
            PolyConstraint newConstraint = this.getPolynomialConstraint(constraint, variables);
            variables.retainAll(newConstraint.getPolynomial().getVariables());

            cs.put(newConstraint, variables);
        }

        return cs;
    }

    public void addAutoStrictConstraint(Map<PolyConstraint, Set<String>> poloConstraints) {
        this.addAutoStrictConstraint(poloConstraints,poloConstraints);
    }

    /**
     * builds from the first given constraints the auto-Strict constraint
     * and adds this to the second constraints (destructive):
     * from s1-t1 >/>= 0,..., sn-tn >/>= 0 build (s1-t1 + ... + sn-tn)(0,...,0) > 0
     */
    public void addAutoStrictConstraint(Map<PolyConstraint, Set<String>> poloFromConstraints, Map<PolyConstraint, Set<String>> poloToConstraints) {
        Polynomial p = Polynomial.ZERO;
        // sum up everything
        for (Entry<PolyConstraint, Set<String>> entry : poloFromConstraints.entrySet()) {
            PolyConstraint pc = entry.getKey();
            Set<String> vars = entry.getValue();
            Polynomial sMinusT = pc.getPolynomial();
            // replace bound vars by zero
            for (String var : vars) {
                sMinusT = sMinusT.setVariableToZero(var);
            }
            p = p.plus(sMinusT);
        }
        PolyConstraint asc = PolyConstraint.create(p,AbstractConstraint.GR);
        Set<String> variables = new LinkedHashSet<String>();
        poloToConstraints.put(asc, variables);
    }

    public Polynomial getPolynomialFromFunction(SyntacticFunctionSymbol symbol, int degree) {
        int arity = symbol.getArity();

        Polynomial[] coeffs = new Polynomial[symbol.getArity()];
        Arrays.fill(coeffs, Polynomial.ZERO);

        Polynomial[] variables = new Polynomial[arity];
        for (int i = 0; i < arity; ++i) {
            variables[i] = Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + (i + 1));
        }

        Polynomial sum = this.coefficientFactory.nextVariable();

        if ((degree == Interpretation.SIMPLE) || ((degree == Interpretation.SIMPLE_MIXED) && (symbol.getArity() != 1))) {

            int numberOfAddends = (int) Math.pow(2, arity);

            for (int i = 1; i < numberOfAddends; ++i) {
                Polynomial variable = this.coefficientFactory.nextVariable();
                Polynomial addend = variable;

                for (int j = 0; j < arity; ++j) {
                    int exponent = (i >> j) & 1;
                    if (exponent == 1) {
                        addend = addend.times(variables[j]);
                        coeffs[j] = coeffs[j].plus(variable);
                    }
                }

                sum = sum.plus(addend);
            }

        } else if (degree == Interpretation.SIMPLE_MIXED) {

            Polynomial variable = this.coefficientFactory.nextVariable();
            coeffs[0] = coeffs[0].plus(variable);
            sum = sum.plus(variable.times(variables[0]));

            variable = this.coefficientFactory.nextVariable();
            coeffs[0] = coeffs[0].plus(variable);
            sum = sum.plus(variable.times(variables[0].power(2)));

        } else {

            int numberOfAddends = (int) Math.pow(degree + 1, arity);

            for (int i = 1; i < numberOfAddends; ++i) {
                int remainder = i;
                int sumOfExponents = 0;
                int[] exponents = new int[arity];

                for (int j = arity - 1; j >= 0; --j) {
                    exponents[j] = (int) (remainder / Math.pow(degree + 1, j));
                    remainder -= (int) Math.pow(degree + 1, j) * exponents[j];
                    sumOfExponents += exponents[j];
                }

                if (sumOfExponents <= degree) {
                    Polynomial variable = this.coefficientFactory.nextVariable();
                    Polynomial addend = variable;

                    for (int j = 0; j < arity; ++j) {
                        if (exponents[j] >= 1) {
                            addend = addend.times(variables[j].power(exponents[j]));
                            coeffs[j] = coeffs[j].plus(variable);
                        }
                    }

                    sum = sum.plus(addend);
                }
            }
        }

        this.coefficients.put(symbol, coeffs);

        return sum;
    }

    public static Polynomial specialize(Map<String, Integer> state, Polynomial p) {
        for (Iterator innerIter = state.entrySet().iterator(); innerIter.hasNext();) {
            Entry innerEntry = (Entry) innerIter.next();
            p =
                p.substituteVariable(
                        (String) innerEntry.getKey(),
                        Polynomial.createConstant(((Integer) innerEntry.getValue()).intValue()));
        }
        return p;
    }

    /**
     * Calculates a new Interpretation as the specialization of the current one.
     * sets all coefficients to value in given state.
     * Those coefficients not occurring in the state will be set to defValue
     * @param state
     * @param defValue
     */
    public Interpretation specialize(Map<String, Integer> state, int defValue) {
        Interpretation specialization =
            new Interpretation(CoefficientFactory.create(new HashSet()));

        for (Entry<SyntacticFunctionSymbol, Polynomial> entry : this.entrySet()) {

            SyntacticFunctionSymbol function = entry.getKey();
            Polynomial polynomial = entry.getValue();

            polynomial = Interpretation.specialize(state,polynomial);

            // replace remaining coefficients by default Value
            // first detect coefficients
            Set coeffs = polynomial.getVariables();
            for (int i = 0; i < function.getArity(); ++i) {
                coeffs.remove(Interpretation.VARIABLE_PREFIX + (i + 1));
            }

            // then do the replacement
            if (defValue < 0) {
                defValue = 0;
            }
            Polynomial defVal = Polynomial.createConstant(defValue);
            for (Iterator i = coeffs.iterator(); i.hasNext();) {
                polynomial = polynomial.substituteVariable((String)i.next(),defVal);
            }

            specialization.put(entry.getKey(), polynomial);
        }

        return specialization;
    }


    @Override
    public boolean isEmpty() {

        boolean tmp = this.entrySet().isEmpty();
        return tmp;

    }


    @Override
    public String export(Export_Util eu) {
        if (eu instanceof PLAIN_Util) {
            return this.toString();
        } else if (eu instanceof HTML_Util) {
            return this.toHTML();
        } else if (eu instanceof LaTeX_Util) {
            return this.toLaTeX();
        } else {
            return this.toString();
        }
    }


    public String toHTML() {

        StringBuffer buffer = new StringBuffer("Polynomial interpretation:\n");

        buffer.append("<blockquote><table border=0>\n");

        for (Iterator iter = this.entrySet().iterator(); iter.hasNext();) {
            Entry entry = (Entry) iter.next();

            SyntacticFunctionSymbol function = (SyntacticFunctionSymbol) entry.getKey();
            buffer.append("<tr><td>");

            // ugly hack for correct alignment
            buffer.append("<sub>&nbsp;</sub><sup>&nbsp;</sup>");

            buffer.append("POL(<b>");

            if (function.getFixity() == SyntacticFunctionSymbol.INFIX ||
                    function.getFixity() == SyntacticFunctionSymbol.INFIXL ||
                    function.getFixity() == SyntacticFunctionSymbol.INFIXR) {
                buffer.append(Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + "1").toHTML());
                buffer.append(" " + function.getName() + " ");
                buffer.append(Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + "2").toHTML());
            }
            else {
                buffer.append(function.getName());
                if (function.getArity() > 0) {
                    buffer.append("(");
                    for (int i = 0; i < function.getArity(); ++i) {
                        if (i > 0) {
                            buffer.append(", ");
                        }
                        buffer.append(Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + (i + 1)).toHTML());
                    }
                    buffer.append(")");
                }
            }

            buffer.append("</b>)</td><td>= &nbsp;");
            buffer.append(((Polynomial) entry.getValue()).toHTML());

            // again the ugly hack
            buffer.append("<sub>&nbsp;</sub><sup>&nbsp;</sup>");

            buffer.append("</td></tr>\n");
        }
        buffer.append("</table></blockquote>");

        return buffer.toString();
    }

    public String toLaTeX() {
        StringBuffer buffer = new StringBuffer("Polynomial interpretation:\n");

        buffer.append("\\begin{eqnarray*}\n");

        for (Iterator iter = this.entrySet().iterator(); iter.hasNext();) {
            Entry entry = (Entry) iter.next();

            SyntacticFunctionSymbol function = (SyntacticFunctionSymbol) entry.getKey();
            String fname = function.toLaTeX();
            buffer.append("POL(");

            if (function.getFixity() == SyntacticFunctionSymbol.INFIX ||
                    function.getFixity() == SyntacticFunctionSymbol.INFIXL ||
                    function.getFixity() == SyntacticFunctionSymbol.INFIXR) {
                buffer.append(Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + "1").toLaTeX());
                buffer.append("\\mathsf{ " + fname + " }");
                buffer.append(Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + "2").toLaTeX());
            }
            else {
                buffer.append("\\mathsf{"+fname+"}");

                if (function.getArity() > 0) {
                    buffer.append("(");
                    for (int i = 0; i < function.getArity(); ++i) {
                        if (i > 0) {
                            buffer.append(", ");
                        }
                        buffer.append(Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + (i + 1)).toLaTeX());
                    }
                    buffer.append(")");
                }
            }

            buffer.append(") &=&");
            buffer.append(((Polynomial) entry.getValue()).toLaTeX());

            if (iter.hasNext()) {
                buffer.append("\\\\\n");
            }
        }

        buffer.append("\n\\end{eqnarray*}\n");

        return buffer.toString();
    }

    @Override
    public String toString() {
        StringBuffer buffer = new StringBuffer("Polynomial interpretation:\n");

        for (Iterator iter = this.entrySet().iterator(); iter.hasNext();) {
            Entry entry = (Entry) iter.next();

            SyntacticFunctionSymbol function = (SyntacticFunctionSymbol) entry.getKey();

            buffer.append("POL(");

            if (function.getFixity() == SyntacticFunctionSymbol.INFIX ||
                    function.getFixity() == SyntacticFunctionSymbol.INFIXL ||
                    function.getFixity() == SyntacticFunctionSymbol.INFIXR) {
                buffer.append(Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + "1"));
                buffer.append(" " + function.getName() + " ");
                buffer.append(Polynomial.createVariable(Interpretation.VARIABLE_PREFIX + "2"));
            }
            else {
                buffer.append(function.getName());

                if (function.getArity() > 0) {
                    buffer.append("(");
                    for (int i = 0; i < function.getArity(); ++i) {
                        if (i > 0) {
                            buffer.append(", ");
                        }
                        buffer.append(Interpretation.VARIABLE_PREFIX + (i + 1));
                    }
                    buffer.append(")");
                }
            }

            buffer.append(") = ");
            buffer.append(entry.getValue());
            buffer.append("\n");
        }

        return buffer.toString();
    }
}
