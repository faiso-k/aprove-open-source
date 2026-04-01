package aprove.verification.dpframework;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.prooftree.Obligations.Junctors.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.oldframework.Logic.*;
import immutables.*;

public class ResultFactory {

    /**
     * Return failure result.
     * NotApplicable means we cannot apply this kind of processor
     * to the given obligation, e.g., try to prove a formula with
     * a DP-Problem Processor.
     */
    public static Result notApplicable() {
        return ResultFactory.notApplicable("(no reason)");
    }

    /**
     * Return failure result.
     * NotApplicable means we cannot apply this kind of processor
     * to the given obligation, e.g., try to prove a formula with
     * a DP-Problem Processor.
     */

    public static Result notApplicable(String reason) {
        return ResultFactory.failure("NOTAP: " + reason);
    }

    /**
     * Return failure result.
     * Aborted means we can possible apply this processor
     * to the given obligation, but we were aborted.
     */
    public static Result aborted(AbortionException e) {
        return ResultFactory.aborted(e.getMessage());
    }
    public static Result aborted(String reason) {
        return ResultFactory.failure("ABORT: " + reason);
    }

    /**
     * Returns an error-result, which indicates that
     * some error occurred during the calculation
     * of the processor.
     * @param message - an error description, i.e., an exception-message
     */
    public static Result error(Throwable reason) {
        return ResultFactory.error("Thrown " + reason.toString());
    }
    public static Result error(String message) {
        return ResultFactory.failure("ERROR: " + message);
    }

    /**
     * Returns failure result.
     * Unsuccessful means, we have tried it, there was no
     * resource limit, but we were not able to handle this
     * obligation.
     */
    public static Result unsuccessful() {
        return ResultFactory.unsuccessful("(no reason)");
    }

    public static Result unsuccessful(String reason) {
        return ResultFactory.failure("UNSUC: " + reason);
    }


    /**
     * Failure result. Up to now no info can be stored here.
     * @return
     */
    private static Result failure(String explanation) {
        return new StandardResult(null, new Fail(explanation));
    }


    /**
     * proven where we have to continue on the todo obligation,
     * and the new proof-obligation is the todo
     */
    public static Result proved(BasicObligation todo, Implication direction, Proof proof) {
        BasicObligationNode obl = new BasicObligationNode(todo);
        return new StandardResult(obl, direction, proof);
    }

    /**
     * proven with Result TRUE and nothing else to show
     */
    public static Result proved(Proof proof) {
        List<BasicObligation> nothing = Collections.emptyList();
        return ResultFactory.provedWithJunctor(nothing, Junctors.YES, YNMImplication.EQUIVALENT, proof);
    }

    /**
     * proven with Result NO and nothing else to show
     */
    public static Result disproved(Proof proof) {
        List<BasicObligation> nothing = Collections.emptyList();
        return ResultFactory.provedWithJunctor(nothing, Junctors.NO, YNMImplication.COMPLETE, proof);
    }

    /**
     * not proven/disproven, thus result is MAYBE      
     */
    public static Result unknown(Proof proof) {
        List<BasicObligation> nothing = Collections.emptyList();
        return ResultFactory.provedWithJunctor(nothing, Junctors.MAYBE, YNMImplication.EQUIVALENT, proof);
    }
    
    /**
     * proven with a fixed, arbitrary TruthValue
     */
    public static Result provedWithValue(TruthValue tv, Proof proof) {
        List<BasicObligationNode> nothing = Collections.emptyList();
        return new StandardResult(nothing, new ProofFinished(), proof, Junctors.FIXED_VALUE(tv));
    }

    /**
     * proven with a fixed, arbitrary TruthValue, and an Implication
     */
    public static Result provedWithValueAndImplication(TruthValue tv, Implication implication, Proof proof) {
        List<BasicObligationNode> nothing = Collections.emptyList();
        return new StandardResult(nothing, implication, proof, Junctors.FIXED_VALUE(tv));
    }

    /**
     * proven where we have to continue on all todos, and
     * the new proof-obligation is the conjunction of all todos
     */
    public static Result provedAnd(Collection<? extends BasicObligation> todos, Implication direction, Proof proof) {
        return ResultFactory.provedWithJunctor(todos, Junctors.AND, direction, proof);
    }

    /**
     * proven where we have to continue on the second obligation only, and a proof for the first is given
     */
    public static Result provedAnd(BasicObligationNode one, BasicObligation two, Implication direction, Proof proof) {
        List<BasicObligationNode> oneTwo = new ArrayList<BasicObligationNode>(2);
        BasicObligationNode twoN = new BasicObligationNode(two);
        oneTwo.add(one);
        oneTwo.add(twoN);
        ObligationNode obl = JunctorObligationNode.createAnd(oneTwo);
        ObligationNodeChild oblc = new ObligationNodeChild(obl, proof, direction);
        ExecutableStrategy strat = new Success(twoN);
        return new StandardResult(oblc, strat);
    }


    /**
     * proven where we have to continue on all todos, and
     * the new proof-obligation is the disjunction of all todos
     */
    public static Result provedOr(Collection<? extends BasicObligation> todos, Implication direction, Proof proof) {
        return ResultFactory.provedWithJunctor(todos, Junctors.OR, direction, proof);
    }

    /**
     * proven where we have to compute the max upper bound on all obligations
     */
    public static Result provedMax(Collection<? extends BasicObligation> todos, Implication direction, Proof proof) {
        return ResultFactory.provedWithJunctor(todos, Junctors.MAX_UPPER, direction, proof);
    }

    /**
     * proven where we have to compute the min upper bound on all obligations
     */
    public static Result provedMin(Collection<? extends BasicObligation> todos, Implication direction, Proof proof) {
        return ResultFactory.provedWithJunctor(todos, Junctors.MIN_UPPER, direction, proof);
    }

    /**
     * proven where we have to compute the multiplication of upper bounds on all obligations
     */
    public static Result provedMult(Collection<? extends BasicObligation> todos, Implication direction, Proof proof) {
        return ResultFactory.provedWithJunctor(todos, Junctors.MULT_UPPER, direction, proof);
    }

    /**
     * proven where we have to continue on todos cond and obl, and
     * the new proof-obligation is the COND of those todos.
     */
    public static Result provedCond(BasicObligation cond, BasicObligation obl, Implication direction, Proof proof) {
        Collection<BasicObligationNode> obls = new ArrayList<BasicObligationNode>(2);
        obls.add(new BasicObligationNode(cond));
        obls.add(new BasicObligationNode(obl));

        return new StandardResult(obls, direction, proof,Junctors.COND);
    }

    public static Result provedWithJunctor(Collection<? extends BasicObligation> todos, IJunctor junctor, Implication direction, Proof proof) {
        Collection<BasicObligationNode> obls = new ArrayList<BasicObligationNode>(todos.size());
        for (BasicObligation bo : todos) {
            obls.add(new BasicObligationNode(bo));
        }
        return new StandardResult(obls, direction, proof, junctor);
    }

    public static Result provedAndFromOblNodes(Collection<? extends BasicObligationNode> todos, Implication direction, Proof proof) {
        return new StandardResult(todos, direction, proof, Junctors.AND);
    }

    public static Result provedOrFromOblNodes(Collection<? extends BasicObligationNode> todos, Implication direction, Proof proof) {
        return new StandardResult(todos, direction, proof, Junctors.OR);
    }

    public static Result provedWithNewStrategy(ObligationNode node, Implication direction, Proof proof, ExecutableStrategy exStr) {
        return new StandardResult(new ObligationNodeChild(node, proof, direction), exStr);
    }

    public static Result provedAndWithNewStrategy(Collection<? extends ObligationNode> andPieces,
            Implication direction, Proof proof, ExecutableStrategy exStr) {
        return ResultFactory.provedWithNewStrategy(JunctorObligationNode.createAnd(andPieces), direction, proof, exStr);
    }

    public static Result provedOrWithNewStrategy(Collection<? extends ObligationNode> orPieces,
            Implication direction, Proof proof, ExecutableStrategy exStr) {
        return ResultFactory.provedWithNewStrategy(JunctorObligationNode.createOr(orPieces), direction, proof, exStr);
    }

    public static Result provedAndJunctorObligations(Collection<? extends ObligationNode> junctors, Collection<? extends BasicObligationNode> positions,
            Implication direction, Proof proof) {
        return new StandardResult(junctors, positions, direction,proof,Junctors.AND);
    }
    public static Result provedOrJunctorObligations(Collection<? extends ObligationNode> junctors, Collection<? extends BasicObligationNode> positions,
            Implication direction, Proof proof) {
        return new StandardResult(junctors, positions, direction,proof,Junctors.OR);
    }


    public static Result justANewStrategy(ExecutableStrategy exStr) {
        return new StandardResult(null, exStr);
    }


    static class StandardResult implements Result {
        final ObligationNodeChild oblImpProof;
        final ExecutableStrategy strategy;

        public StandardResult(BasicObligationNode obl, Implication direction, Proof proof) {
            List<BasicObligationNode> strat = new ArrayList<BasicObligationNode>(1);
            strat.add(obl);
            this.strategy = new Success(ImmutableCreator.create(strat));
            this.oblImpProof = new ObligationNodeChild( obl, proof, direction );
        }

        public StandardResult(BasicObligationNode obl, Collection<? extends BasicObligationNode> positions, Implication direction, Proof proof) {
            this.strategy = new Success(positions);
            this.oblImpProof = new ObligationNodeChild( obl, proof, direction );
        }

        public StandardResult(Collection<? extends BasicObligationNode> obls, Implication direction, Proof proof, IJunctor junctor) {
            this.strategy = new Success(obls);

            ObligationNode oblNode = JunctorObligationNode.create(junctor, obls);

            this.oblImpProof = new ObligationNodeChild( oblNode, proof, direction );
        }

        public StandardResult(Collection<? extends ObligationNode> obls, Collection<? extends BasicObligationNode> positions,
                Implication direction, Proof proof, IJunctor junctor ) {
            this.strategy = new Success(positions);

            ObligationNode oblNode = JunctorObligationNode.create(junctor, obls);

            this.oblImpProof = new ObligationNodeChild( oblNode, proof, direction );
        }

        public StandardResult(ObligationNodeChild oblImpProof, ExecutableStrategy exStr) {
            this.oblImpProof = oblImpProof;
            this.strategy = exStr;
        }

        @Override
        public ExecutableStrategy getStrategy() {
            return this.strategy;
        }
        @Override
        public ObligationNodeChild getObligationChild() {
            return this.oblImpProof;
        }

        @Override
        public BasicObligationNode getSuccessPosition() {
            if (! (this.strategy instanceof Success)) {
                throw new IllegalArgumentException("Result does not contain Success");
            }
            List<BasicObligationNode> positions = ((Success)this.strategy).getPositions();
            if (positions.size() != 1) {
                throw new IllegalArgumentException("getSuccessPosition ambiguous: " +
                        "have " +positions.size() + "success positions");
            }
            return positions.get(0);
        }
    }



}
