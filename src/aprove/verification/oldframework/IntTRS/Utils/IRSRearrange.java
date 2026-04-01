package aprove.verification.oldframework.IntTRS.Utils;

import aprove.Globals;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Utilities to rearrange TRS-Terms into other more canonical forms
 *   
 * @author Alex Hoppen
 */
public class IRSRearrange {
    
    /**
     * Converts the given term to an equivalent term of the form variable = rearrangedTerm.
     * 
     * The implementation of this rearrange algorithm is not complete but covers most cases.
     * If rearranging failed, null is returned.
     * 
     * This assumes that term is an as compound term with the binary function symbol "="
     * 
     * @param term The term to rearrange such that variable stands alone on the lhs
     * @param variable The variable to move to the lhs
     * @return A rearranged term with variable on the lhs or null if the rearrange failed
     */
    public static TRSTerm rearrangeTermToVariable(TRSFunctionApplication term, TRSVariable variable) {
        if (Globals.useAssertions) {
            assert ((TRSCompoundTerm)term).getFunctionSymbol().getArity() == 2;
            assert ((TRSCompoundTerm)term).getFunctionSymbol().getName().equals("=");
        }
        // Change term1 = term2 to the form 0 = term1 - term2 as it is expected for rearrangeTermToVariableImpl
        TRSTerm rhs = TRSTerm.createFunctionApplication(FunctionSymbol.create("-", 2), term.getArgument(0), term.getArgument(1));
        Pair<TRSTerm, TRSTerm> rearranged = rearrangeTermToVariableImpl(rhs, variable);
        if (rearranged != null) {
            rearranged = simplify(rearranged);
            rearranged = cleanLhs(rearranged);
            if (rearranged != null) {
                return rearranged.y;
            } else {
                return null;
            }
        } else {
            return null;
        }
    }
    
    /**
     * Recursive implementation to rearrange a term such that one specific variable is the only 
     * variable on the left-hand-side and all other variables and constant only occur on 
     * the right-hand-side
     * 
     * It assumes to be given a term of the form 0 = term It then recursively descends
     * the term tree and returns a pair such that pair.x = pair.y is equivalent to  to 0 = term
     * 
     * Note that the left-hand-side may still be a compound expression, 
     * e.g. -(var), -(-(var)) or (var + var)
     * 
     * If the expression is to complex to be resolved using this algorithm, null is returned.
     * 
     * Currently the only supported function symbols are binary + and - and unary -
     * 
     * @param term The term to rearrange such that the given variable is the only variable on the lhs
     * @param variable The variable to move to the lhs
     * @return null if rearranging failed or a pair where x is the lhs of an assignment and only 
     * contains the given variable and y is the rhs containing all other variables and constants.
     * Each component of the pair may be null if the corresponding side is empty.
     */
    private static Pair<TRSTerm, TRSTerm> rearrangeTermToVariableImpl(TRSTerm term, TRSVariable variable) {
        if (term instanceof TRSVariable) {
            if (term == variable) {
                return new Pair<TRSTerm, TRSTerm>(TRSTerm.createFunctionApplication(FunctionSymbol.create("-", 1), term), null);
            } else {
                return new Pair<TRSTerm, TRSTerm>(null, term);
            }
        } else if (term instanceof TRSConstantTerm) {
            return new Pair<TRSTerm, TRSTerm>(null, term);
        } else if (term instanceof TRSCompoundTerm) {
            TRSCompoundTerm compoundTerm = (TRSCompoundTerm)term;
            FunctionSymbol functionSymbol = compoundTerm.getFunctionSymbol();
            if (functionSymbol.getName().equals("+")) {
                if (Globals.useAssertions) {
                    assert functionSymbol.getArity() == 2;
                }
                // Rebase the operands of + separately
                final Pair<TRSTerm, TRSTerm> rearrangedLhs = rearrangeTermToVariableImpl(compoundTerm.getArgument(0), variable);
                final Pair<TRSTerm, TRSTerm> rearrangedRhs = rearrangeTermToVariableImpl(compoundTerm.getArgument(1), variable);
                
                if (rearrangedLhs == null || rearrangedRhs == null) {
                    return null;
                }
                
                // Combine the results of rearranging the operands of +
                final TRSTerm resultLhs;
                final TRSTerm resultRhs;
                if (rearrangedLhs.x != null && rearrangedRhs.x != null) {
                    resultLhs = TRSTerm.createFunctionApplication(functionSymbol, rearrangedLhs.x, rearrangedRhs.x);
                } else if (rearrangedLhs.x != null && rearrangedRhs.x == null) {
                    resultLhs = rearrangedLhs.x;
                } else if (rearrangedLhs.x == null && rearrangedRhs.x != null) {
                    resultLhs = rearrangedRhs.x;
                } else {
                    resultLhs = null;
                }
                
                if (rearrangedLhs.y != null && rearrangedRhs.y != null) {
                    resultRhs = TRSTerm.createFunctionApplication(functionSymbol, rearrangedLhs.y, rearrangedRhs.y);
                } else if (rearrangedLhs.y != null && rearrangedRhs.y == null) {
                    resultRhs = rearrangedLhs.y;
                } else if (rearrangedLhs.y == null && rearrangedRhs.y != null) {
                    resultRhs = rearrangedRhs.y;
                } else {
                    resultRhs = null;
                }
                return new Pair<TRSTerm, TRSTerm>(resultLhs, resultRhs);
            } else if (functionSymbol.getName().equals("-")) {
                if (Globals.useAssertions) {
                    assert functionSymbol.getArity() == 2;
                }
                // Rebase the operands of - separately
                final Pair<TRSTerm, TRSTerm> rearrangedLhs = rearrangeTermToVariableImpl(compoundTerm.getArgument(0), variable);
                final Pair<TRSTerm, TRSTerm> rearrangedRhs = rearrangeTermToVariableImpl(compoundTerm.getArgument(1), variable);
                
                if (rearrangedLhs == null || rearrangedRhs == null) {
                    return null;
                }
                
                // Combine the results of rearranging the operands of -
                final TRSTerm resultLhs;
                final TRSTerm resultRhs;
                if (rearrangedLhs.x != null && rearrangedRhs.x != null) {
                    resultLhs = TRSTerm.createFunctionApplication(functionSymbol, rearrangedLhs.x, rearrangedRhs.x);
                } else if (rearrangedLhs.x != null && rearrangedRhs.x == null) {
                    resultLhs = rearrangedLhs.x;
                } else if (rearrangedLhs.x == null && rearrangedRhs.x != null) {
                    resultLhs = TRSTerm.createFunctionApplication(FunctionSymbol.create("-", 1), rearrangedRhs.x);
                } else {
                    resultLhs = null;
                }
                
                if (rearrangedLhs.y != null && rearrangedRhs.y != null) {
                    resultRhs = TRSTerm.createFunctionApplication(functionSymbol, rearrangedLhs.y, rearrangedRhs.y);
                } else if (rearrangedLhs.y != null && rearrangedRhs.y == null) {
                    resultRhs = rearrangedLhs.y;
                } else if (rearrangedLhs.y == null && rearrangedRhs.y != null) {
                    resultRhs = TRSTerm.createFunctionApplication(FunctionSymbol.create("-", 1), rearrangedRhs.y);
                } else {
                    resultRhs = null;
                }
                return new Pair<TRSTerm, TRSTerm>(resultLhs, resultRhs);
            } else {
                return null;
            }
        } else {
            return null;
        }
    }
    
    /**
     * Takes an assignment as a pair (pair.x = pair.y) and tries to bring it into a canonical
     * form var = term where var is a single variable.
     * 
     * If this was not possible null is returned.
     * 
     * Currently the following measures are taken to clean the LHS:
     * <ul>
     *   <li> Change -var = term to var = -term 
     * </ul>
     * 
     * @param assignment The assignment in which the LHS should be cleaned to only contain a 
     * single variable
     * @return A cleaned assignment where pair.x instanceof TRSVariable or null if the assignment
     * could not be transformed to this form
     */
    public static Pair<TRSTerm, TRSTerm> cleanLhs(Pair<TRSTerm, TRSTerm> assignment) {
        if (assignment.x instanceof TRSVariable) {
            return assignment;
        } else if (assignment.x instanceof TRSFunctionApplication) {
            TRSFunctionApplication functionApplication = (TRSFunctionApplication)assignment.x;
            FunctionSymbol functionSymbol = functionApplication.getFunctionSymbol();
            if (functionSymbol.getName().equals("-") && functionSymbol.getArity() == 1) {
                if (functionApplication.getArgument(0) instanceof TRSVariable) {
                    return new Pair<TRSTerm, TRSTerm>(functionApplication.getArgument(0), TRSTerm.createFunctionApplication(functionSymbol, assignment.y));
                } else {
                    return null;
                }
            } else {
                return null;
            }
        } else {
            return null;
        }
    }
    
    /**
     * Applies {@link #simplify(TRSTerm)} to both elements in the pair
     * @param assignment The pair to simplify
     * @return A new pair where each member is simplified according to {@link #simplify(TRSTerm)}
     */
    private static Pair<TRSTerm, TRSTerm> simplify(Pair<TRSTerm, TRSTerm> assignment) {
        TRSTerm lhs = assignment.x;
        TRSTerm rhs = assignment.y;
        if (lhs != null) {
            lhs = lhs.simplify();
        }
        if (rhs != null) {
            rhs = rhs.simplify();
        }
        return new Pair<TRSTerm, TRSTerm>(lhs, rhs);
    }
}
