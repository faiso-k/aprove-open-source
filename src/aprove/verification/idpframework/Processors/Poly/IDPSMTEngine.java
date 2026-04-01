package aprove.verification.idpframework.Processors.Poly;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;

/**
 *
 * @author MP
 */
public interface IDPSMTEngine<C extends SemiRing<C>> {

    // ###############################################################################
    // # Non-Linear part
    // ###############################################################################
    public Map<IVariable<C>, Signum> getVarSignum(final ItpfConjClause precondition,
        final PolyInterpretation<C> interpretation,
        final Abortion aborter) throws AbortionException;

    /**
     * Maybe approximation only
     */
    public boolean isUnsolvable(final ItpfConjClause precondition,
        final PolyInterpretation<C> interpretation,
        final Abortion aborter) throws AbortionException;

    // ###############################################################################
    // # Linear part, using linear SMT solver
    // ###############################################################################
    public Set<ItpfConjClause> getLinearSolvableClauses(final Itpf precondition,
        final PolyInterpretation<C> interpretation,
        final Abortion aborter) throws AbortionException;

    public Map<IVariable<C>, Signum> getLinearVarSignum(final ItpfConjClause precondition,
        final PolyInterpretation<C> interpretation,
        final Abortion aborter) throws AbortionException;

    public boolean isLinearPartSolvable(final ItpfConjClause precondition,
        final PolyInterpretation<C> interpretation,
        final Abortion aborter)  throws AbortionException;

}