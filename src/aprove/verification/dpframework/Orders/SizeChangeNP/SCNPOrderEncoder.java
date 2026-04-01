package aprove.verification.dpframework.Orders.SizeChangeNP;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Interface for encoders from term constraints to SAT.
 *
 * Can essentially be used to convert atoms from "SAT modulo
 * term constraints" and from QActiveConditions to intermediate
 * formulae and from there to pure SAT.
 *
 * Probably most handy if you intend to work with the NP fragment
 * of size change.
 *
 * @author Carsten Fuhs, Peter Schneider-Kamp
 */
public interface SCNPOrderEncoder {

    /**
     * Will be called <i>before</i> the first call to <code>encode()</code>.
     *
     * @param sig signature for the base encoder to work on
     * @param aborter
     * @return a formula that will be used as side conjunct for the
     *  overall formula
     * @throws AbortionException
     */
    Formula<None> pre(Set<FunctionSymbol> sig,
            Abortion aborter) throws AbortionException;

    /**
     * Encodes a term constraint to SAT. In most cases, this method
     * will be called multiple times, so your implementation should be
     * stateful and keep needed information (such as the intended
     * semantics of certain propositional variables).
     *
     * Note to users: Some SCNPOrderEncoders may only accept terms
     * with symbols from a signature they have been initialized with.
     *
     * @param c - "s > t" or "s >= t"
     * @param aborter
     * @return a formula that becomes true iff the constraint <code>c</code>
     *  holds
     * @throws AbortionException
     */
    Formula<None> encode(Constraint<TRSTerm> c, Abortion aborter)
        throws AbortionException;

    /**
     * Will be called <i>after</i> the last call to <code>encode()</code>.
     *
     * @param aborter
     * @return a formula that will be used as side conjunct for the
     *  overall formula
     */
    Formula<None> post(Abortion aborter) throws AbortionException;

    /**
     * Will be called after all calls to pre()/encode*()/post() on:
     *
     * pre(...) and <something featuring some of encode(...)> and post(...)
     *
     * Can be used, e.g., to convert POFormula-in-disguise
     * to actual Formula<None>.
     *
     * @param f - a formula that may need some finalization (e.g., because
     *  some variables with special meaning -- like Fact -- may want to be
     *  transformed)
     * @param aborter
     * @return a formula that can (and will) be fed to a SAT solver
     * @throws AbortionException
     */
    Formula<None> toFinalFormula(Formula<None> f,
            Abortion aborter) throws AbortionException;

    /**
     * @param f - a function symbol beknownst to the SCNPOrderEncoder
     *  (so no tuple symbol, unless we consider extended size-change graphs)
     * @param i - an argument position of f
     * @param aborter
     * @return a formula expressing that f regards its i-th argument.
     * @throws AbortionException
     */
    Formula<None> encodeQActiveAtom(FunctionSymbol f, int i, Abortion aborter) throws AbortionException;

    /**
     * Synthesizes the order that you get from a given <code>satModel</code>
     * (list of true and false subformulas, where exactly the positive
     * numbers denote that the subformula of that number is true) based on
     * the particular semantics of some of the prop. variables/formulas
     * used by the TermConstraintSATEncoder.
     *
     * @param satModel
     * @param aborter
     * @return the order corresponding to satModel and the internal state
     * @throws AbortionException
     */
    QActiveOrder decode(int[] satModel, Abortion aborter)
        throws AbortionException;

    /**
     * @return the FormulaFactory used internally to construct
     *  propositional formulas
     */
    FormulaFactory<None> getFormulaFactory();
}
