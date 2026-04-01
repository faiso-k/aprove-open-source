package aprove.verification.dpframework.Orders.Utility.PMATRO;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.PolyMatrices.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Polynomial interpretation of terms, where the coefficients are
 * nxn-matrices over C (except for the constant addend, which is
 * a nx1-matrix, i.e., a "column vector").
 *
 * One can often also make use of the optimization to "collapse"
 * interpretations for the "tuple symbols" of P (if P and R have a
 * suitable shape, i.e., they fulfill the "tuple symbol condition"):
 * Then the coefficients for tuple symbols are 1xn-matrices
 * ("line vectors"), and the constant addend is a 1x1-matrix.
 * For non-tuple-symbols, nothing changes.
 *
 * Variables are also interpreted as nx1-matrices.
 * The actual representation is through matrices with polynomials
 * as entries, not vice versa, for ease of use. Any computations
 * done on matrices are purely symbolical; they are broken down
 * into individual sub-constraints before the actual encoding
 * takes place.
 *
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public abstract class AbstractPolyMatrixInterpretation<C extends GPolyCoeff> implements Exportable,
        CPFAdditional
{

    /**
     * The (semi-)ring that the matrix entries come from.
     */
    protected final Semiring<C> ringC;

    /**
     * A factory for matrix entries, which are polynomials over C.
     */
    protected final OrderPolyFactory<C> entryPolyFactory;

    /**
     * A factory for matrices whose entries are polynomials over C.
     */
    protected final PolyMatrixFactory<C> matrixFactory;

    /**
     * A factory for polynomial constraints.
     */
    protected final ConstraintFactory<C> constraintFactory;

    /**
     * The mapping from function symbols to their interpretations.
     * Each interpretation is automatically collapsed to a
     * single column vector with polynomials as entries.
     */
    protected final Map<FunctionSymbol, PolyMatrix<C>> pol = new LinkedHashMap<FunctionSymbol, PolyMatrix<C>>();

    /**
     * The mapping from function symbols to the "pure" polynomial form
     * of their interpretations (effectively, a sum of matrix*var
     * monomials). Only used for displaying.
     */
    protected final Map<FunctionSymbol, Map<GPolyVar, PolyMatrix<C>>> actualPol =
        new LinkedHashMap<FunctionSymbol, Map<GPolyVar, PolyMatrix<C>>>();

    /**
     * The usable rule constraints will be pre-generated and cached here
     * because constructing them at a later point in time would require
     * lots of unnecessary digging in structures that have been dealt with before.
     */
    protected Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<C>> usableRuleConstraints =
        new LinkedHashMap<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<C>>();

    /**
     * A flattening visitor to operate on outer polynomials.
     */
    protected final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter;

    /**
     * The dimension of the matrices used in the interpretation.
     */
    protected final int dimension;

    /**
     * If true, require all pairs to be oriented strictly. Otherwise,
     * require only one to be oriented strictly and all others at
     * least weakly.
     */
    protected final boolean allstrict;

    /**
     * A set of constraints expressing that the interpretation must be
     * extended monotone, i.e., the strict greater relation must be
     * monotone in addition to the weak one.
     */
    protected final Set<OrderPolyConstraint<C>> extendedMonotonicityConstraint =
        new LinkedHashSet<OrderPolyConstraint<C>>();

    /**
     * Set of symbols whose application is interpreted as a number/polynomial,
     * not as a vector of numbers/polynomials. Often the so-called "tuple
     * symbols" of P.
     */
    protected final Set<FunctionSymbol> collapsingSyms;

    /**
     * A variable substitution. This is populated by specialize()
     * and holds the matrix entries' actual values as computed
     * by, e.g., a SAT solver.
     */
    protected Map<GPolyVar, C> model = null;

    /**
     * The papers explaining how this specific interpretation works.
     */
    protected final List<Citation> citations;

    /**
     * Some text describing this specific interpretation,
     * e.g. "with entries of type C".
     */
    protected final String description;

    public static final String VARIABLE_PREFIX = "x_";
    public static final String ENTRY_PREFIX = "a_";
    public static final String ACTIVE_PREFIX = "b_";
    private int nextEntry = 1;

    /**
     * For XML export, the "type" attribute of the <matro> tag.
     */
    protected String matroType;

    /**
     * For XML export, additional attributes of the <matro> tag.
     */
    protected final Map<XMLAttribute, String> xmlOptions = new LinkedHashMap<XMLAttribute, String>();

    protected AbstractPolyMatrixInterpretation(final Semiring<C> ringC, final OrderPolyFactory<C> entryPolyFactory,
            final PolyMatrixFactory<C> matrixFactory, final ConstraintFactory<C> constraintFactory,
            final FlatteningVisitor<GPoly<C, GPolyVar>, GPolyVar> fvOuter, final int dimension,
            final boolean allstrict, final Set<FunctionSymbol> collapsingSyms, final String description,
            final List<Citation> citations) {
        this.ringC = ringC;
        this.entryPolyFactory = entryPolyFactory;
        this.matrixFactory = matrixFactory;
        this.constraintFactory = constraintFactory;
        this.fvOuter = fvOuter;
        this.dimension = dimension;
        this.allstrict = allstrict;
        this.collapsingSyms = collapsingSyms;
        this.description = description;
        this.citations = citations;
    }

    /**
     * Returns the name of the next available coefficient identifier.
     * The result is used for /all/ entries of a matrix/vector by
     * the matrix factory, which must add indexes to the name.
     */
    protected String getNextCoeffName() {
        return AbstractPolyMatrixInterpretation.ENTRY_PREFIX + (this.nextEntry++);
    }

    /**
     * Generate an interpretation for the given symbol if it does
     * not already have one.
     */
    public void extend(final FunctionSymbol symbol) {
        if (!this.pol.containsKey(symbol)) {
            final boolean collapse = this.collapsingSyms.contains(symbol);
            final Triple<PolyMatrix<C>, Map<GPolyVar, PolyMatrix<C>>, Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<C>>> inters =
                this.getMatrixFromFunction(symbol, collapse);
            this.pol.put(symbol, inters.x);
            this.actualPol.put(symbol, inters.y);
            this.usableRuleConstraints.putAll(inters.z);
        }
    }

    /**
     * Generate interpretations for the function symbols occurring
     * in the given constraint.
     */
    public void extend(final Constraint<TRSTerm> constraint) {
        for (final FunctionSymbol fSym : constraint.getLeft().getFunctionSymbols()) {
            this.extend(fSym);
        }
        for (final FunctionSymbol fSym : constraint.getRight().getFunctionSymbols()) {
            this.extend(fSym);
        }
    }

    abstract public Triple<PolyMatrix<C>, Map<GPolyVar, PolyMatrix<C>>, Map<Pair<FunctionSymbol, Integer>, OrderPolyConstraint<C>>> getMatrixFromFunction(final FunctionSymbol symbol,
        boolean collapse);

    /**
     * Create a set of active rule conditions for a given coeff matrix.
     * Note that a rule with a QAC of (f/n) is usable iff the n-th argument
     * of f has a coefficient that is somewhere non-zero.
     *
     * @param coeffMatrix A coefficient matrix from this interpretation
     * @return A set of constraints whose disjunction expresses that some
     *  entry of the matrix is not equal to 0 (0 being the neutral element
     *  of the addition operation in the current semi-ring).
     */
    protected Set<OrderPolyConstraint<C>> generateActiveConditions(final PolyMatrix<C> coeffMatrix) {
        final int rows = coeffMatrix.numRows();
        final int cols = coeffMatrix.numCols();
        final Set<OrderPolyConstraint<C>> result = new LinkedHashSet<OrderPolyConstraint<C>>(rows * cols);
        final OrderPoly<C> zeroPoly =
            this.entryPolyFactory.buildFromCoeff(this.entryPolyFactory.getInnerFactory().buildFromCoeff(
                this.ringC.zero()));

        for (int j = 0; j < rows; j++) {
            for (int k = 0; k < cols; k++) {
                final OrderPoly<C> entryPoly = coeffMatrix.get(j, k);
                result.add(this.constraintFactory.createNot(this.constraintFactory.createWithQuantifier(entryPoly,
                    zeroPoly, ConstraintType.EQ)));
            }
        }
        return result;
    }

    /**
     * Returns the polynomial constraints resulting from interpreting
     * the terms as matrices and then comparing the entries pairwise.
     */
    abstract public OrderPolyConstraint<C> fromTermConstraints(final Collection<Constraint<TRSTerm>> constraints,
        Abortion aborter) throws AbortionException;

    /**
     * Interprets the given term as a matrix of polynomials.
     */
    public PolyMatrix<C> interpretTerm(final TRSTerm t, final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert ((t instanceof TRSFunctionApplication) || (t instanceof TRSVariable));
            // if other terms should ever be created, the below code
            // needs to be checked
        }
        if (t.isVariable()) { // easy: Variable
            return this.matrixFactory.buildVariableVector(t.getName());
        } else { // FunctionApplication
            // compute the interpretations of the arguments of t ...
            final TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
            if (args.isEmpty()) { // fApp is a constant
                return this.pol.get(fApp.getRootSymbol());
            }
            final int size = args.size();
            final Map<GPolyVar, GPoly<GPoly<C, GPolyVar>, GPolyVar>> substitution =
                new LinkedHashMap<GPolyVar, GPoly<GPoly<C, GPolyVar>, GPolyVar>>(size);
            for (int i = 0; i < size; ++i) {
                aborter.checkAbortion();
                final PolyMatrix<C> argMatrix = this.interpretTerm(args.get(i), aborter);
                for (int j = 0; j < this.dimension; j++) {
                    final String argVarString = AbstractPolyMatrixInterpretation.VARIABLE_PREFIX + (i + 1) + "#" + (j + 1);
                    final GPolyVar argVar = GAtomicVar.createVariable(argVarString);
                    substitution.put(argVar, argMatrix.at(j, 0).unwrap());
                }
            }
            // ... then get the interpretation of the root symbol
            final PolyMatrix<C> rootMatrix = this.pol.get(fApp.getRootSymbol());
            // and plug the arg polys into the root polys
            return this.matrixFactory.substituteVariables(rootMatrix, substitution, aborter);
        }
    }

    /**
     * Create the constraints defining the active-ness of rules and create the
     * constraints for the rules based on that.
     * @param usableRules The rules with the corresponding active condition.
     * @param aborter some aborter.
     * @return A constraint which includes all constraints for the active
     * conditions and the constraints for the usable rules.
     * @throws AbortionException when the aborter kicks in.
     */
    public OrderPolyConstraint<C> getActiveRuleConstraints(final Map<? extends GeneralizedRule, QActiveCondition> usableRules,
        final Abortion aborter) throws AbortionException {

        // build active usable rules constraints
        final Set<OrderPolyConstraint<C>> activeConstraints = new LinkedHashSet<OrderPolyConstraint<C>>();

        // extend signature
        for (final GeneralizedRule rule : usableRules.keySet()) {
            for (final FunctionSymbol f : rule.getFunctionSymbols()) {
                this.extend(f);
            }
        }

        // build constraints
        for (final Map.Entry<? extends GeneralizedRule, QActiveCondition> usable : usableRules.entrySet()) {
            aborter.checkAbortion();
            final QActiveCondition qac = usable.getValue();
            final GeneralizedRule rule = usable.getKey();
            final Constraint<TRSTerm> ruleConstraint = Constraint.fromRule(rule, OrderRelation.GE);
            final Set<Constraint<TRSTerm>> rcSet = Collections.singleton(ruleConstraint);
            final OrderPolyConstraint<C> polyRuleConstraint = this.fromTermConstraints(rcSet, aborter);
            if (qac != QActiveCondition.TRUE) {
                final Set<OrderPolyConstraint<C>> conjConstraints = new LinkedHashSet<OrderPolyConstraint<C>>();
                for (final Set<Pair<FunctionSymbol, Integer>> andCondition : qac.getSetRepresentation()) {
                    aborter.checkAbortion();
                    final Set<OrderPolyConstraint<C>> atomicConstraints = new LinkedHashSet<OrderPolyConstraint<C>>();
                    for (final Pair<FunctionSymbol, Integer> aCond : andCondition) {
                        atomicConstraints.add(this.usableRuleConstraints.get(aCond));
                    }
                    conjConstraints.add(this.constraintFactory.createAnd(atomicConstraints));
                }
                // the QActiveConstraint is in disjunctive normal form,
                // so rebuild the original structure
                final OrderPolyConstraint<C> disjConstraint = this.constraintFactory.createOr(conjConstraints);
                // if the constraint from the QACs is fulfilled, then the rule constraint must be, too
                activeConstraints.add(this.constraintFactory.createOr(this.constraintFactory.createNot(disjConstraint),
                    polyRuleConstraint));
            } else {
                final OrderPolyConstraint<C> trivialConstraint = this.constraintFactory.createFalse();
                activeConstraints.add(this.constraintFactory.createOr(polyRuleConstraint, trivialConstraint));
            }
        }
        return this.constraintFactory.createAnd(activeConstraints);
    }

    /**
     * @param f - a function symbol beknownst to this interpretation
     * @param i - an argument position of f
     * @param aborter
     * @return a constraint expressing that f regards its i-th argument.
     * @throws AbortionException
     */
    public OrderPolyConstraint<C> encodeQActiveAtom(final FunctionSymbol f, final int i, final Abortion aborter)
            throws AbortionException {
        final Pair<FunctionSymbol, Integer> fi = new Pair<FunctionSymbol, Integer>(f, i);
        OrderPolyConstraint<C> res = this.usableRuleConstraints.get(fi);
        final Set<GPolyVar> eVars = res.getFreeVariables();
        res = this.constraintFactory.createQuantifierE(res, eVars);
        return res;
    }

    /**
     * Determine whether an Active Rule Condition is satisfied.
     * Can only be used after specialization.
     * @param condition Some QActiveCondition.
     * @param coeffOrder An order to determine whether values are ZERO.
     * @return true iff the given condition is fulfilled.
     */
    public boolean solvesQActiveConstraint(final QActiveCondition condition, final CoeffOrder<C> coeffOrder) {

        if (condition == QActiveCondition.TRUE) {
            return true;
        }
        if (Globals.useAssertions) {
            assert (this.model != null);
        }
        for (final Set<Pair<FunctionSymbol, Integer>> andCondition : condition.getSetRepresentation()) {
            boolean conjunctFulfilled = true;
            for (final Pair<FunctionSymbol, Integer> condAtom : andCondition) {
                final OrderPolyConstraint<C> orConstraint = this.usableRuleConstraints.get(condAtom);
                Set<OrderPolyConstraint<C>> constraints;
                if (orConstraint instanceof OPCOr) {
                    constraints = ((OPCOr<C>) orConstraint).getOperands();
                } else { // if dimension = 1
                    constraints = Collections.singleton(orConstraint);
                }
                boolean someCoeffIsNonZero = false;
                for (final OrderPolyConstraint<C> constraint : constraints) {
                    // constraint should have the shape
                    //   not( A( a_i = ZERO ) )
                    if (Globals.useAssertions) {
                        assert constraint instanceof OPCNot;
                    }

                    final OrderPolyConstraint<C> aConstraint = ((OPCNot<C>) constraint).getSub();
                    if (Globals.useAssertions) {
                        assert aConstraint instanceof OPCQuantifierA;
                    }
                    OrderPolyConstraint<C> actualConstraint;
                    actualConstraint = ((OPCQuantifierA<C>) aConstraint).getInnerConstraint();
                    if (Globals.useAssertions) {
                        assert (actualConstraint instanceof OPCAtom) : "Error: atom expected, found: "
                            + actualConstraint;
                    }
                    final OrderPoly<C> poly = ((OPCAtom<C>) actualConstraint).getLeftPoly();
                    final GPolyVar var = poly.getInnerPoly().getVariables().iterator().next();
                    final C value = this.model.get(var);
                    if (!coeffOrder.equal(value, this.ringC.zero())) {
                        someCoeffIsNonZero = true;
                    }
                    // the above code is quite tailor-made for the specific
                    // shape of our qac-encoding for matrices; using an
                    // evaluation visitor for OPCs instead would probably
                    // be nicer
                }
                if (!someCoeffIsNonZero) {
                    conjunctFulfilled = false;
                }
            }
            if (conjunctFulfilled) {
                return true;
            }
        }
        return false;
    }

    /**
     * Exports the mapping from function symbols to polynomials with matrix coefficients.
     *
     * @param eu the export util
     * @return the exported version of the interpretation
     */
    @Override
    public String export(final Export_Util eu) {
        final StringBuilder result = new StringBuilder("Matrix interpretation ");
        if (this.description.length() < 1) {
            /*this.citations.add(0, Citation.MATRO);
            result.append(eu.cite(this.citations.toArray(
                    new Citation[this.citations.size()])));*/
            result.append(eu.cite(Citation.MATRO));
        } else {
            result.append(eu.cite(Citation.MATRO) + " " + this.description + " "
                + eu.cite(this.citations.toArray(new Citation[this.citations.size()])));
        }
        result.append(":\n");

        final int size = this.actualPol.size();
        final List<String> rows = new ArrayList<String>(size);

        for (final Map.Entry<FunctionSymbol, Map<GPolyVar, PolyMatrix<C>>> entry : this.actualPol.entrySet()) {
            final List<String> rowEntries = new ArrayList<String>();
            final StringBuilder sb = new StringBuilder("POL(");
            final FunctionSymbol functionSymbol = entry.getKey();
            final int arity = functionSymbol.getArity();

            // display function symbol with argument list
            final StringBuilder functionWithVars = new StringBuilder(functionSymbol.export(eu));
            if (arity > 0) {
                functionWithVars.append("(");
                for (int i = 1; i <= arity; ++i) {
                    final String var = AbstractPolyMatrixInterpretation.VARIABLE_PREFIX + i;
                    functionWithVars.append(this.exportVarName(var, eu));
                    if (i < arity) {
                        functionWithVars.append(", ");
                    }
                }
                functionWithVars.append(")");
            }

            // append polynomial interpretation
            sb.append(functionWithVars.toString());
            sb.append(") = ");
            rowEntries.add(sb.toString());
            final Map<GPolyVar, PolyMatrix<C>> monomials = entry.getValue();
            int i = 1;
            for (final Map.Entry<GPolyVar, PolyMatrix<C>> monomial : monomials.entrySet()) {
                if (monomial.getKey() == null) {
                    rowEntries.add(monomial.getValue().export(eu));
                } else {
                    rowEntries.add(monomial.getValue().export(eu));
                    rowEntries.add(eu.multSign());
                    rowEntries.add(eu.bold(this.exportVarName(monomial.getKey().getName(), eu)));
                }
                if (i < monomials.size()) {
                    rowEntries.add(" + ");
                }
                ++i;
            }
            final StringBuilder line = new StringBuilder();
            line.append(eu.tableStart(rowEntries.size()));
            line.append(eu.tableRow(rowEntries));
            line.append(eu.tableEnd());
            // line.append(eu.linebreak());
            rows.add(line.toString());
        }

        result.append(eu.set(rows, Export_Util.RULES));
        return result.toString();
    }

    protected String exportVarName(final String varName, final Export_Util eu) {
        final String[] elements = varName.split("_");
        String name = elements[0];
        if (elements.length > 1) {
            name += eu.sub(elements[1]);
        }
        return name;
    }

    /**
     * @return a simple string representation.
     */
    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element interpretation = CPFTag.INTERPRETATION.createElement(doc);

        final Element type = CPFTag.TYPE.createElement(doc);
        final Element matrixInterpretation = CPFTag.MATRIX_INTERPRETATION.createElement(doc);
        final Element domain = CPFTag.DOMAIN.create(doc);
        final boolean arctic;
        if (this.matroType.equals("int")) {
            // TODO: check whether ceta also works on naturals
            // the case distinction was introduced since Rainbow demands naturals here
            final CPFTag dom = Options.certifier.isCeta() ? CPFTag.INTEGERS : CPFTag.NATURALS;
            domain.appendChild(dom.create(doc));
            arctic = false;
        } else if (this.matroType.equals("arctic")) {
            final boolean bz = this.xmlOptions.get(XMLAttribute.BELOW_ZERO).equals("true");
            domain.appendChild(CPFTag.ARCTIC.create(
                doc,
                CPFTag.DOMAIN.create(doc, (bz ? CPFTag.INTEGERS : CPFTag.NATURALS).create(doc))));
            arctic = true;
        } else {
            throw new RuntimeException(" unknown matroTypo: "
                + this.matroType
                + " in "
                + this.getClass().getCanonicalName());
        }
        final Element dimensionTag = CPFTag.DIMENSION.createElement(doc);
        dimensionTag.appendChild(doc.createTextNode("" + this.dimension));

        matrixInterpretation.appendChild(domain);
        matrixInterpretation.appendChild(dimensionTag);
        final Element strictDim = CPFTag.STRICT_DIMENSION.createElement(doc);
        strictDim.appendChild(doc.createTextNode("1"));
        matrixInterpretation.appendChild(strictDim);
        type.appendChild(matrixInterpretation);
        interpretation.appendChild(type);

        for (final Map.Entry<FunctionSymbol, Map<GPolyVar, PolyMatrix<C>>> fun : this.actualPol.entrySet()) {
            final FunctionSymbol symbol = fun.getKey();
            final Map<GPolyVar, PolyMatrix<C>> monomials = fun.getValue();

            final Element interTag = CPFTag.INTERPRET.createElement(doc);
            interTag.appendChild(symbol.toCPF(doc, xmlMetaData));
            final Element arity = CPFTag.ARITY.createElement(doc);
            arity.appendChild(doc.createTextNode("" + symbol.getArity()));
            interTag.appendChild(arity);

            final Element polyTag = CPFTag.POLYNOMIAL.createElement(doc);
            final Element sum = CPFTag.SUM.createElement(doc);
            for (final Map.Entry<GPolyVar, PolyMatrix<C>> monomial : monomials.entrySet()) {
                final PolyMatrix<C> matrix = monomial.getValue();
                final GPolyVar var = monomial.getKey();
                final Element product = CPFTag.PRODUCT.createElement(doc);
                matrix.setDimension(this.dimension);
                product.appendChild(matrix.toCPF(doc, xmlMetaData, arctic));
                if (var instanceof XMLObligationExportable) {
                    final Element variable = CPFTag.VARIABLE.createElement(doc);
                    variable.appendChild(doc.createTextNode(((XMLObligationExportable) var).toString().substring(2)));
                    final Element polynomialOfVariable = CPFTag.POLYNOMIAL.createElement(doc);
                    polynomialOfVariable.appendChild(variable);
                    product.appendChild(polynomialOfVariable);
                }
                sum.appendChild(CPFTag.POLYNOMIAL.create(doc, product));
            }
            polyTag.appendChild(sum);

            interTag.appendChild(polyTag);
            interpretation.appendChild(interTag);
        }

        final Element oCP = CPFTag.ORDERING_CONSTRAINT_PROOF.createElement(doc);
        final Element redPair = CPFTag.RED_PAIR.createElement(doc);
        redPair.appendChild(interpretation);
        oCP.appendChild(redPair);

        return oCP;
    }

    /**
     * Substitute the coefficient variables of a polynomial
     * according to the given map.
     * @param polynomial The polynomial.
     * @param state The map defining the substutution.
     * @return An OrderPoly where the variables inside the
     * coefficients are substituted according to state.
     */
    protected OrderPoly<C> deepSubstitute(final OrderPoly<C> polynomial,
        final Map<GPolyVar, C> state,
        final Abortion aborter) throws AbortionException {
        final Map<GPolyVar, GPoly<C, GPolyVar>> subst = new LinkedHashMap<GPolyVar, GPoly<C, GPolyVar>>(state.size());
        final VarPartNode<GPolyVar> varOne = this.entryPolyFactory.getVarOne();

        // provide a map that can be used for substitutions over GPOLYs.
        for (final Map.Entry<GPolyVar, C> entry : state.entrySet()) {
            final GPolyVar var = entry.getKey();
            final C coeff = entry.getValue();
            final GPoly<C, GPolyVar> substPoly = this.entryPolyFactory.getInnerFactory().concat(coeff, varOne);
            subst.put(var, substPoly);
        }

        final Map<GPoly<C, GPolyVar>, GPoly<C, GPolyVar>> coeffMap =
            new LinkedHashMap<GPoly<C, GPolyVar>, GPoly<C, GPolyVar>>();
        // substitute in each coefficient
        for (final GPoly<C, GPolyVar> coeff : polynomial.getCoeffs()) {
            if (coeff != null) {
                GPoly<C, GPolyVar> result = coeff;
                result =
                    this.entryPolyFactory.getInnerFactory().substituteVariables(result, subst, this.ringC, aborter);

                // take care that the new coeff will be used in the final result
                if (!coeff.equals(result)) {
                    coeffMap.put(coeff, result);
                }
            }
        }

        // build a new (outer) polynomial with the new coefficients
        OrderPoly<C> result = polynomial;
        for (final Map.Entry<GPoly<C, GPolyVar>, GPoly<C, GPolyVar>> entry : coeffMap.entrySet()) {
            result = this.entryPolyFactory.substituteCoefficient(result, entry.getKey(), entry.getValue(), null);
        }
        return result;
    }

    /**
     * Return a constraint that ensures the interpretation to be extended monotone.
     */
    public OrderPolyConstraint<C> getExtendedMonotonicityConstraint() {
        return this.constraintFactory.createAnd(this.extendedMonotonicityConstraint);
    }
}
