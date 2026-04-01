package aprove.verification.dpframework.IDPProblem.Processors.cgirp;

import java.util.*;

import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public interface INodeConditionFunction {

    public List<ImmutablePair<ConditionalConstraint, DefaultProof>> createNodeCondition(IDPProblem idp, Node dp, Itpf conclusion, Abortion aborter) throws AbortionException;

}
