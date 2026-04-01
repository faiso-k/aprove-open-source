package aprove.verification.oldframework.Bytecode.Natives;

import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ObjectRefinement.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * This is the base class of all classes implementing the semantics of a predefined (i.e., native or overwritten)
 * method.
 *
 * <pre>
 * Predefined methods behave a lot like opcodes:
 *   - They transform a given state into one or more new states
 *   - This transformation can either be a refine, throwing an exception
 *     or simple evaluation
 * </pre>
 *
 * For predefined methods we assume that no further method is called by them, so
 * there cannot be any recursion involving a predefined method.
 * @author Christian von Essen.
 */
public abstract class PredefinedMethod {

    public Optional<List<String>> getArgs() {
        return Optional.empty();
    }

    static SimplePolynomial instantiate(SimplePolynomial pol, List<String> args, State s) {
        ArrayList<AbstractVariableReference> origStack = s.getCurrentStackFrame().getOperandStack().getStack();
        List<AbstractVariableReference> stack = new ArrayList<>(origStack).subList(origStack.size() - args.size(), origStack.size());
        Map<String, String> sigma = args.stream().collect(toMap(x -> x, x -> stack.remove(0).toString()));
        return pol.replace(sigma);
    }

    void addSizeBound(State s, EdgeInformation e, AbstractVariableReference r, Optional<SimplePolynomial> lowerBound, Optional<SimplePolynomial> upperBound) {
        if (getArgs().isPresent()) {
            if (upperBound.isPresent()) {
                SimplePolynomial upperSizeBound = instantiate(upperBound.get(), getArgs().get(), s);
                e.add(new SizeRelationInformation(r, IntegerRelationType.LE, upperSizeBound));
            }
            if (lowerBound.isPresent()) {
                SimplePolynomial lowerSizeBound = instantiate(lowerBound.get(), getArgs().get(), s);
                e.add(new SizeRelationInformation(r, IntegerRelationType.GE, lowerSizeBound));
            }
        }
    }

    /**
     * <p><b>NOTE</b>: You need to pass the uncloned original state, as possible
     * split results are lost in cloning.</p>
     *
     * @param s Input state
     * @param result Object used for collecting the result
     * @return true if refinement was needed and done, false if no refinement was needed
     */
    public boolean refine(final State s, final Collection<Pair<State, ? extends EdgeInformation>> result) {
        return false;
    }

    /**
     * <p><b>IMPORTANT</b>: May only be called if the corresponding {@link
     * #refine(State, Collection)} returns false for the same input state
     * (i.e., only if no refinement is needed)</p>
     *
     * <p><b>NOTE</b>: You need to pass the uncloned original state, as possible
     * split results are lost in cloning.</p>
     *
     * @param s Input state
     * @return State and information of the result of the opcode's operation on the input state
     */
    public abstract Pair<State, ? extends EdgeInformation> evaluate(final State s);

    /**
     * @param preEval some state.
     * @param postEval state obtained from <code>preEval</code> by plain
     * evaluation.
     * @param postEvalInst instance of <code>postEval</code>.
     * @param refMap mapping from references in <code>postEval</code> to their
     *  counterparts in <code>postEvalInst</code>.
     *
     * @return <code>preEvalInst</code>, an instance of <code>preEval</code>
     *  such that <code>postEvalInst</code> is obtained from it by plain
     *  evaluation.
     */
    public State reverseEvaluation(
        final State preEval,
        final State postEval,
        final State postEvalInst,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap)
    {
        throw new NotYetImplementedException();
    }

    public boolean isApplicable(State s) {
        return true;
    }
}
