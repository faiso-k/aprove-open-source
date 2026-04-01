/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Replaces predefined context sensitive symbols
 * @author mpluecke
 *
 */
@Deprecated
public class InfRuleIdpReplacePredefSymbols extends InfRuleToPoly {

    public InfRuleIdpReplacePredefSymbols() {
        super();
    }

    @Override
    public InfRuleID getID() {
        return InfRuleID.REPLACE_CONTEXT_PREDEF_FUNCTIONS;
    }

    @Override
    public String getLongName() {
        return "REPLACE_CONTEXT_PREDEF_FUNCTIONS: replaces predefined functions with context sensitive interpretations";
    }

    @Override
    public String getName() {
        return "REPLACE_CONTEXT_PREDEF_FUNCTIONS";
    }

    /*
    @Override
    protected Constraint buildAtom(Term left, RelDependency kLeft, Term right, RelDependency kRight, RelDependency uRight, ConstraintType relation, boolean replaceTermsByArbitraryConstants, TermAtom termAtom, Abortion aborter) throws AbortionException {
        if (termAtom != null) {
            if (kLeft != null || kRight != null) {
                IDPGInterpretation interpretation = (IDPGInterpretation)getIrc().getPolyInterpretation();
                Term newL;
                if (kLeft != null) {
                    Pair<RelDependency, Stack<ImmutablePair<FunctionSymbol, Integer>>> stack = new Pair<RelDependency, Stack<ImmutablePair<FunctionSymbol, Integer>>>(kLeft, new Stack<ImmutablePair<FunctionSymbol, Integer>>());
                    newL = replaceAllFunctionSymbols(termAtom.getLeft(), interpretation, stack);
                } else {
                    newL = termAtom.getLeft();
                }
                Term newR;
                if (kRight != null) {
                    Pair<RelDependency, Stack<ImmutablePair<FunctionSymbol, Integer>>> stack = new Pair<RelDependency, Stack<ImmutablePair<FunctionSymbol, Integer>>>(kRight, new Stack<ImmutablePair<FunctionSymbol, Integer>>());
                    newR = replaceAllFunctionSymbols(termAtom.getRight(), interpretation, stack);
                } else {
                    newR = termAtom.getRight();
                }
                return termAtom.change(newL, newR);
            } else {
                return termAtom;
            }
        } else {
            throw new IllegalArgumentException("Need term atoms");
        }
    }

    @Override
    protected Constraint buildConclusionAtom(GeneralizedRule rule, Term left, Term right, Kind kind, Predicate termAtom, Abortion aborter) throws AbortionException {
        if (kind == Kind.AbstractRelationEQ) {
            return buildAtom(left, termAtom.getULeft(), right, termAtom.getURight(), ms, ConstraintType.GE, false, termAtom, aborter);
        }
        if (kind == Kind.AbstractRelation) {
            return buildAtom(left, termAtom.getULeft(), right, termAtom.getURight(), ms, ConstraintType.GE, false, termAtom, aborter);
        } else if (kind == Kind.NonInfConstantCompare) {
            return buildAtom(left, RelDependency.Decreasing, right, null, ms, ConstraintType.GE, false, termAtom, aborter);
        } else {
            throw new UnsupportedOperationException("unsupported kind");
        }
    }

    @Override
    protected Constraint hadleEquality(FunctionApplication reduceLeft, ReducesTo reducesTo, Abortion aborter) throws AbortionException {
        return reducesTo;
    }

    */
    public final TRSTerm replaceAllFunctionSymbols(
        TRSTerm t,
        IDPGInterpretation interpretation,
        Pair<RelDependency, Stack<ImmutablePair<FunctionSymbol, Integer>>> kPathToRoot
    ) {
        if (t.isVariable()) {
            return t;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        FunctionSymbol replacement = interpretation.getContextReplacementSymbol(fs, kPathToRoot);
        // System.err.println("replacement: " + fs + " " + replacement);
        boolean changed;
        if (replacement == null) {
            replacement = fs;
            changed = false;
        } else {
            changed = true;
        }
        ImmutableList<? extends TRSTerm> args = fa.getArguments();
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
        int toSize = fs.getArity();
        for (int i = 0; i < toSize; i++) {
            TRSTerm arg = args.get(i);
            kPathToRoot.y.push(new ImmutablePair<FunctionSymbol, Integer>(fs, i));
            TRSTerm newArg = this.replaceAllFunctionSymbols(arg, interpretation, kPathToRoot);
            if (newArg != arg) {
                changed = true;
            }
            newArgs.add(newArg);
            kPathToRoot.y.pop();
        }
        if (changed) {
            return TRSTerm.createFunctionApplication(replacement, ImmutableCreator.create(newArgs));
        } else {
            return t;
        }
    }

}
