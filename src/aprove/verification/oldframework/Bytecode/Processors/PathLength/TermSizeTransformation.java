package aprove.verification.oldframework.Bytecode.Processors.PathLength;

import java.math.*;
import java.util.*;

import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Apply term size transformation to a single rule.
 *
 * @author Felix Bier
 */
public class TermSizeTransformation {

    /** Rule to be transformed. */
    private final IGeneralizedRule rule;

    /** Resulting rule. */
    private IGeneralizedRule result;

    /** Utility for detecting predefined symbols. */
    private final PathLengthUtil util;

    /** Symbols standing on the lhs of some rule of the system. */
    private final Set<FunctionSymbol> definedSymbols;

    /** Collect a list of conditions that resemble the patterns
     * formed by constructor terms on the lhs. */
    private final List<TRSTerm> patternConditions;

    public TermSizeTransformation(IGeneralizedRule currentRule,
                                  PathLengthUtil util, Set<FunctionSymbol> definedSymbols) {
        this.rule = currentRule;
        this.util = util;
        this.definedSymbols = definedSymbols;
        this.result = null;
        this.patternConditions = new ArrayList<>();
    }

    /**
     * Apply term size transformation to the rule.
     * @return the transformed rule
     */
    public IGeneralizedRule transform() {
        if (this.result == null) {
            this.result = this.rewriteObjects(this.rule);
        }

        return this.result;
    }

    /**
     * Apply term size transformation to the lhs and rhs.
     * @param rule to be transformed
     * @return the transformed rule
     */
    private IGeneralizedRule rewriteObjects(IGeneralizedRule rule) {
        final TRSTerm left = rule.getLeft();
        final TRSTerm right = rule.getRight();
        final TRSTerm cond = rule.getCondTerm();

        final TRSTerm newLeft = this.rewriteObjectsInTerm(left, true);
        final TRSTerm newRight = this.rewriteObjectsInTerm(right, false);

        TRSTerm newCond = cond;

        final FunctionSymbol andSymbol = this.util.getPredefinedMap().getSym(Func.Land, DomainFactory.BOOLEAN);

        for (final TRSTerm constraint : this.patternConditions) {
            if (newCond == null) {
                newCond = constraint;
            } else {
                newCond = TRSTerm.createFunctionApplication(andSymbol, newCond, constraint);
            }
        }

        return IGeneralizedRule.create((TRSFunctionApplication) newLeft, newRight, newCond);
    }

    /* Recursively replace terms encoding objects by integers. */
    private TRSTerm rewriteObjectsInTerm(TRSTerm term, boolean collectPatterns) {
        // TODO: END_OF_CLASS, CYCLIC_INSTANCE_TERM?

        /* If term is variable, we are done. Otherwise ... */
        if (term.isVariable()) {
            return term;
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication)term;
            FunctionSymbol fs = fa.getRootSymbol();

            if (fs.equals(this.util.NULL)) {
                TRSTerm zero = this.util.getIntFunc(BigInteger.ZERO);
                return zero;
            } else if (fs.equals(this.util.ARRAY_CONSTR)) {
                /* Array constructor contains a single variable
                   depicting the arrays size. */
                TRSTerm arraysize = fa.getArgument(0);
                return arraysize;
            } else {
                /* Some function symbol. Convert arguments first. */
                ArrayList<TRSTerm> subterms = new ArrayList<>();

                for (int i = 0; i < fs.getArity(); i++) {
                    TRSTerm child = fa.getArgument(i);

                    TRSTerm newChild = this.rewriteObjectsInTerm(child, collectPatterns);

                    subterms.add(newChild);
                }

                /* Now put them together according to function symbol. */

                if (CpxIntTermHelper.isComSymbol(fs)) {
                    /* Compound symbol, grouping top level terms on the rhs. */

                    /* Compound symbol may only have function
                     * applications as arguments. */
                    List<TRSFunctionApplication> args = new ArrayList<>();

                    for (TRSTerm t : subterms) {
                        if (t instanceof TRSFunctionApplication) {
                            TRSFunctionApplication fa2 = (TRSFunctionApplication)t;
                            FunctionSymbol fs2 = fa2.getRootSymbol();

                            if (this.definedSymbols.contains(fs2)) {
                                args.add(fa2);
                            }
                        }
                    }

                    TRSTerm com = CpxIntTermHelper.createCom(args);
                    return com;
                } else if (this.definedSymbols.contains(fs) ||
                           this.util.isPredefined(fs)) {
                    /* Defined symbol, don't change. */
                    TRSTerm fa2 = TRSTerm.createFunctionApplication(fs, subterms);
                    return fa2;
                } else {
                    /* Unknown function symbol, assume constructor. */
                    /* First, sum up sub terms. */
                    TRSTerm sum = null;

                    for (TRSTerm t : subterms) {
                        if (sum == null) {
                            sum = t;
                        } else {
                            sum = this.util.buildAddition(sum, t);
                        }
                    }

                    /* Add a condition representing the
                     * pattern formed by the constructor. */
                    if (collectPatterns && sum != null) {
                        TRSFunctionApplication zero = this.util.getIntFunc(BigInteger.ZERO);
                        TRSTerm ge = this.util.buildGreaterOrEqual(sum, zero);

                        this.patternConditions.add(ge);
                    }

                    TRSTerm res = this.util.getIntFunc(BigInteger.ONE);

                    if (sum != null) {
                        res = this.util.buildAddition(res, sum);
                    }

                    return res;
                }
            }

        }
    }

}
