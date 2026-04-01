package aprove.verification.oldframework.Bytecode.Processors.PathLength;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This class performs the transformation of one rule.
 * @author Matthias Hoelzel
 */
public class RuleTransformation {
    /** Rule to be transformed. */
    private final IGeneralizedRule rule;

    /** Rule to be transformed. */
    private IGeneralizedRule result;

    /** A name generator. */
    private final FreshNameGenerator ng;

    /** PathLengthUtil */
    private final PathLengthUtil util;

    /** The typing we inferred. */
    private final LinkedHashMap<FunctionSymbol, ArrayList<TRSTerm>> typing;

    /**
     * Maps every rule to a list of positions, where objects occur. (Right
     * side!)
     */
    private final LinkedList<Position> rightObjects;

    /** Left object position. */
    private final LinkedList<Position> leftObjects;

    /** The new names for the right side */
    private final LinkedHashMap<Position, TRSVariable> newRightVars;

    /** The new names for the left side */
    private final LinkedHashMap<Position, TRSVariable> newLeftVars;

    /** Right Max-Polynomials. */
    private final LinkedHashMap<Position, MaxPolynomial> rightMaxPolys;

    /** Left Max-Polynomials. */
    private final LinkedHashMap<Position, MaxPolynomial> leftMaxPolys;

    /** List of condition terms */
    private final LinkedList<TRSTerm> constraints;

    /**
     * Constructor
     * @param currentRule the current rule to be transformed
     * @param gen name generator
     * @param types typing
     * @param plu path length helper
     */
    public RuleTransformation(
        final IGeneralizedRule currentRule,
        final FreshNameGenerator gen,
        final LinkedHashMap<FunctionSymbol, ArrayList<TRSTerm>> types,
        final PathLengthUtil plu)
    {
        this.rule = currentRule;
        this.ng = gen;
        this.util = plu;
        this.typing = types;
        this.leftObjects = new LinkedList<Position>();
        this.rightObjects = new LinkedList<Position>();
        this.leftMaxPolys = new LinkedHashMap<Position, MaxPolynomial>();
        this.rightMaxPolys = new LinkedHashMap<Position, MaxPolynomial>();
        this.newLeftVars = new LinkedHashMap<Position, TRSVariable>();
        this.newRightVars = new LinkedHashMap<Position, TRSVariable>();
        this.constraints = new LinkedList<TRSTerm>();
        this.constraints.add(this.rule.getCondTerm());
        this.result = null;
    }

    /**
     * Start the transformation!
     * @return a new rule
     */
    public IGeneralizedRule transform() {
        // Already done?
        if (this.result != null) {
            return this.result;
        }

        this.findObjects();
        this.combineConstraints();
        this.addSimpleConstraints();
        this.createResult();

        return this.result;
    }

    /**
     * Finds the objects.
     */
    private void findObjects() {
        final TRSFunctionApplication left = this.rule.getLeft();
        this.findObjectsInTerm(left, this.leftObjects, this.newLeftVars, this.leftMaxPolys, Position.EPSILON);

        final TRSFunctionApplication right = (TRSFunctionApplication) this.rule.getRight();
        this.findObjectsInTerm(right, this.rightObjects, this.newRightVars, this.rightMaxPolys, Position.EPSILON);

        if (Globals.DEBUG_MATTHIAS) {
            final DebugLogger l = DebugLogger.getLogger("pathlength");
            l.logln("\nWe found some objects:");
            l.logln("Left side:");
            l.logln("leftObjects = " + this.leftObjects);
            l.logln("newLeftVars = " + this.newLeftVars);
            l.logln("leftMaxPolys = " + this.leftMaxPolys);

            l.logln("\nRight side:");
            l.logln("rightObjects = " + this.rightObjects);
            l.logln("newRihgtVars = " + this.newRightVars);
            l.logln("rightMaxPolys = " + this.rightMaxPolys);
        }
    }

    /**
     * Find the objects in a given term.
     * @param t a function application
     * @param list list of positions to be completed
     * @param newNames maps positions to their new names
     * @param maxPolys maps positions to the corresponding max-polynomial
     * @param currentPos should be the current position of t
     */
    private void findObjectsInTerm(
        final TRSFunctionApplication t,
        final LinkedList<Position> list,
        final LinkedHashMap<Position, TRSVariable> newNames,
        final LinkedHashMap<Position, MaxPolynomial> maxPolys,
        final Position currentPos)
    {
        final FunctionSymbol sym = t.getRootSymbol();
        final ArrayList<TRSTerm> types = this.typing.get(sym);

        for (int i = 0; i < sym.getArity(); i++) {
            final Position argPosition = currentPos.append(i);
            final TRSTerm arg = t.getArgument(i);
            if (((types != null) && types.get(i).equals(this.util.JLO_TYPE))
                    || this.util.getType(arg).equals(this.util.JLO_TYPE))
            {
                list.add(argPosition);

                newNames.put(argPosition, TRSTerm.createVariable(this.ng.getFreshName("v", false)));
                final MaxPolynomial maxPoly;
                if (arg.isVariable()) {
                    maxPoly =
                            new MaxPolynomial(
                                VarPolynomial.create(BigInteger.ZERO),
                                VarPolynomial.createVariable(((TRSVariable) arg).getName()));
                } else {
                    maxPoly = this.rewriteObjectTermToMaxTerm(arg);
                }
                maxPolys.put(argPosition, maxPoly);
            } else if (currentPos.equals(Position.EPSILON) && (arg instanceof TRSFunctionApplication)) {
                this.findObjectsInTerm((TRSFunctionApplication) arg, list, newNames, maxPolys, argPosition);
            }
        }
    }

    /**
     * Removes object information in a term and returns the rewritten field as a
     * list of VarPolynomials.
     * @param t current term
     * @return list of VarPolynomials
     */
    private MaxPolynomial rewriteObjectTermToMaxTerm(final TRSTerm t) {
        assert !t.isVariable() : "The term " + t + " is not a object term!";

        final TRSFunctionApplication func = (TRSFunctionApplication) t;
        if (this.util.getType(func).equals(this.util.JLO_TYPE))
        {
            final LinkedHashSet<VarPolynomial> fields = new LinkedHashSet<VarPolynomial>();
            this.collectFields(t, 0, fields);
            return new MaxPolynomial(fields);
        } else {
            assert false : "The term " + t + " is not a object term!";
            return null;
        }
    }

    /**
     * Collect all fields of the given object term.
     * @param t a term
     * @param currentLength current path length
     * @param fields set of fields to be completed
     */
    private void collectFields(final TRSTerm t, final int currentLength, final LinkedHashSet<VarPolynomial> fields) {
        if (t.isVariable()) {
            final TRSVariable v = (TRSVariable) t;
            final String name = v.getName();
            final VarPolynomial vp = VarPolynomial.createVariable(name);
            fields.add(vp.plus(VarPolynomial.create(currentLength)));
        } else {
            final TRSFunctionApplication func = (TRSFunctionApplication) t;
            final FunctionSymbol sym = func.getRootSymbol();
            if (sym.equals(this.util.JAVA_LANG_OBJECT_SYMBOL)) {
                final int newLength = currentLength + 1;
                fields.add(VarPolynomial.create(newLength));
                for (final TRSTerm arg : func.getArguments()) {
                    this.collectFields(arg, newLength, fields);
                }
            } else if (sym.equals(this.util.END_OF_CLASS)) {
                // Do nothing -> interpret with 0.
                return;
            } else if (sym.equals(this.util.NULL)) {
                fields.add(VarPolynomial.create(currentLength));
            } else if (sym.equals(this.util.ARRAY_CONSTR)) {
                fields.add(VarPolynomial.create(currentLength));
                // TODO: Implement me!
                //assert false : "Wait for it!: Arrays!";
            } else if (this.util.isPredefined(sym)) {
                final VarPolynomial vp =
                        ToolBox.intTermToPolynomial(t, this.ng).plus(VarPolynomial.create(currentLength));
                fields.add(vp);
            } else {
                final int newLength = currentLength + 1;
                for (final TRSTerm arg : func.getArguments()) {
                    this.collectFields(arg, newLength, fields);
                }
            }
        }
    }

    /**
     * Use combination of right and left variable constraints in order to
     * generate constraints that speak about rule variables.
     */
    private void combineConstraints() {
        for (final Position rightOPos : this.rightObjects) {
            final MaxPolynomial rightMaxPoly = this.rightMaxPolys.get(rightOPos);

            for (final Position leftOPos : this.leftObjects) {
                final MaxPolynomial leftMaxPoly = this.leftMaxPolys.get(leftOPos);
                BigInteger minimum = null;

                for (final VarPolynomial rightPart : rightMaxPoly.getPolynomials()) {
                    BigInteger found = null;
                    for (final VarPolynomial leftPart : leftMaxPoly.getPolynomials()) {
                        final VarPolynomial diff = leftPart.minus(rightPart);
                        if (diff.isConstant()) {
                            assert found == null : "A max-polynomial should be nice and optimized.";
                            found = diff.getConstantPart().getNumericalAddend();
                        }
                    }
                    if (found == null) {
                        minimum = null;
                        break;
                    } else {
                        minimum = ((minimum == null) || (minimum.compareTo(found) > 0)) ? found : minimum;
                    }
                }

                if (minimum != null) {
                    // We obtain:
                    // Right path length + minimum <= Left path length
                    final TRSVariable rightVar = this.newRightVars.get(rightOPos);
                    final TRSVariable leftVar = this.newLeftVars.get(leftOPos);
                    final FunctionSymbol minimumSym = this.util.getIntSym(minimum);
                    final TRSFunctionApplication minimumTerm = TRSTerm.createFunctionApplication(minimumSym);

                    final TRSTerm rpm = this.util.buildAddition(rightVar, minimumTerm);

                    final TRSFunctionApplication constraint =
                            TRSTerm.createFunctionApplication(
                                this.util.getPredefinedMap().getSym(Func.Le, DomainFactory.INTEGERS),
                                rpm,
                                leftVar);

                    this.constraints.add(constraint);

                    if (Globals.DEBUG_MATTHIAS) {
                        final DebugLogger l = DebugLogger.getLogger("pathlength");
                        l.logln("\nAdded a combined constraint: ");
                        l.logln(constraint);
                    }
                }
            }
        }
    }

    /**
     * Add simple constraints to the list of constraints. Latter will be used to
     * form the new rules.
     */
    private void addSimpleConstraints() {
        this.huntForSimpleConstraints(this.leftObjects, this.leftMaxPolys, this.newLeftVars);
        this.huntForSimpleConstraints(this.rightObjects, this.rightMaxPolys, this.newRightVars);
    }

    /**
     * Hunts for primitive constraints like x >= 5.
     * @param objectPositions the current object position mapping
     * @param maxPolys the current maxPolys mapping
     * @param newVars the new variables mapping
     */
    private void huntForSimpleConstraints(
        final LinkedList<Position> objectPositions,
        final LinkedHashMap<Position, MaxPolynomial> maxPolys,
        final LinkedHashMap<Position, TRSVariable> newVars)
    {

        for (final Position objectPos : objectPositions) {
            final MaxPolynomial maxPoly = maxPolys.get(objectPos);
            for (final VarPolynomial vp : maxPoly.getPolynomials()) {
                if (vp.isConstant()) {
                    final BigInteger bi = vp.getConstantPart().getNumericalAddend();
                    final TRSVariable newVar = newVars.get(objectPos);
                    // Now we can add: newLeftVar >= bi
                    final FunctionSymbol biSym =
                            this.util.getPredefinedMap().getIntSym(BigIntImmutable.create(bi), DomainFactory.INTEGERS);
                    final TRSFunctionApplication biFun = TRSTerm.createFunctionApplication(biSym);
                    final FunctionSymbol geSym = this.util.getPredefinedMap().getSym(Func.Ge, DomainFactory.INTEGERS);
                    final TRSFunctionApplication constraint = TRSTerm.createFunctionApplication(geSym, newVar, biFun);
                    this.constraints.add(constraint);

                    if (Globals.DEBUG_MATTHIAS) {
                        final DebugLogger l = DebugLogger.getLogger("pathlength");
                        l.logln("\nAdded a simple constraint: ");
                        l.logln(constraint);
                    }
                }
            }
        }
    }

    /**
     * Builds the resulting rules.
     */
    private void createResult() {
        TRSTerm left = this.rule.getLeft();
        for (final Position p : this.leftObjects) {
            left = left.replaceAt(p, this.newLeftVars.get(p));
        }

        TRSTerm right = this.rule.getRight();
        for (final Position p : this.rightObjects) {
            right = right.replaceAt(p, this.newRightVars.get(p));
        }

        final LinkedList<TRSTerm> currentConstraints = this.constraints;
        TRSTerm condition = null;
        final FunctionSymbol andSymbol = this.util.getPredefinedMap().getSym(Func.Land, DomainFactory.BOOLEAN);
        final Set<TRSVariable> ruleVariables = left.getVariables();
        ruleVariables.addAll(right.getVariables());
        this.findMoreUsefullConstraints(ruleVariables);

        for (final TRSTerm constraint : currentConstraints) {
            if (condition == null) {
                condition = constraint;
            } else {
                condition = TRSTerm.createFunctionApplication(andSymbol, condition, constraint);
            }
        }

        assert left instanceof TRSFunctionApplication : "Something went badly wrong!";
        this.result = IGeneralizedRule.create((TRSFunctionApplication) left, right, condition);
    }

    /**
     * Finds constraints that only use variables that are in allowedVariables
     * contained.
     * @param allowedVariables set of allowed variables
     */
    private void findMoreUsefullConstraints(final Set<TRSVariable> allowedVariables) {
        for (final Position p : this.leftObjects) {
            final MaxPolynomial maxPoly = this.leftMaxPolys.get(p);
            final TRSVariable v = this.newLeftVars.get(p);
            this.filterMaxTerm(maxPoly, v, allowedVariables);
        }
    }

    /**
     * Filters the current max-term and adds some useful constraints.
     * @param maxPoly current max term
     * @param v the current object variable
     * @param allowedVariables set of allowed variables
     */
    private void filterMaxTerm(final MaxPolynomial maxPoly, final TRSVariable v, final Set<TRSVariable> allowedVariables) {
        for (final VarPolynomial vp : maxPoly.getPolynomials()) {
            final Set<String> occurringVariables = vp.getVariables();
            boolean isAllowed = true;
            for (final String occ : occurringVariables) {
                final TRSVariable occVar = TRSTerm.createVariable(occ);
                if (!allowedVariables.contains(occVar)) {
                    isAllowed = false;
                    break;
                }
            }

            if (isAllowed) {
                final TRSTerm operand = this.util.rewriteVarPolynomialToTerm(vp);
                final TRSFunctionApplication constraint =
                        TRSTerm.createFunctionApplication(
                            this.util.getPredefinedMap().getSym(Func.Ge, DomainFactory.INTEGERS),
                            v,
                            operand);
                this.constraints.add(constraint);

                if (Globals.DEBUG_MATTHIAS) {
                    final DebugLogger l = DebugLogger.getLogger("pathlength");
                    l.logln("\nAdded another constraint: ");
                    l.logln(constraint);
                }
            }
        }
    }
}
