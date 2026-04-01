package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * All implementing classes have the ability to convert two
 * sets of SimplePolyConstraints (normal + searchstrict) to
 * a pair of
 *  - a propositional formula/circuit which is satisfiable iff
 *    the sets of SimplePolyConstraints to be converted
 *    are satisfiable over [0 .. 2^bits - 1] where bits
 *    is the number of bits used to encode each indefinite
 *    coefficient
 *  - a mapping that maps indefinite coefficients to
 *    the corresponding propositional variables
 *    such that each model of the 1st result component
 *    can be used to derive values for the indefinite
 *    coefficients that can be used to satisfy the
 *    SimplePolyConstraints.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public interface PoloSatConverter {

    /**
     * Converts a set of SimplePolyConstraints to be
     * fulfilled as such and a set of searchstrict
     * SimplePolyConstraints to a propositional
     * formula/circuit and a mapping that assigns
     * indefinite coefficients that occur in the
     * constraints to corresponding variables. In
     * case there is a model for the first component of
     * the result, its interpretation of these variables
     * can be used to derive values for the indefinite
     * coefficients of <code>spcs</code> such that all
     * constraints in <code>spcs</code> are satisfied.
     *
     * @param spcs the SimplePolyConstraints to encode
     * @param searchStrictSpcs the searchStrict constraints
     *  (type GE, at least one of them must be oriented strictly),
     *  empty set means "not in searchstrict mode"
     * @return a corresponding propositional formula/Boolean circuit
     *  along with a mapping from indefinite coefficients to the
     *  input variables of the formula/circuit
     * @see convert(Formula<Diophantine>), allows for more general
     *  problem description
     */
    public Pair<Formula<None>, Map<String, PolyCircuit>> convert (Set<SimplePolyConstraint> spcs,
            Set<SimplePolyConstraint> searchStrictSpcs, Abortion aborter) throws AbortionException;

    /**
     * Converts a Formula<Diophantine> to a purely Boolean circuit.
     * Range information is to be taken from the attributes of the
     * implementation as passed to the corresponding
     * <code>create</code> method.
     *
     * @param f - a Formula over Diophantine TheoryPropositions
     *  to be encoded to SAT
     * @return a corresponding purely propositional formula/Boolean
     *  circuit along with a mapping from indefinite coefficients to
     *  the corresponding tuples of subformulae of the formula/circuit
     *  and a mapping of prop. vars of f to the corresponding vars of x
     */
    public Triple<Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> convert(Formula<Diophantine> f,
        Abortion aborter) throws AbortionException;

    /**
     * Converts a Formula<Diophantine> to a purely Boolean circuit.
     * Range information is to be taken from the attributes of the
     * implementation as passed to the corresponding
     * <code>create</code> method.
     *
     * @param f - a Formula over Diophantine TheoryPropositions
     *  to be encoded to SAT
     * @param specialSubformulae - we want their conversion results explicitly,
     *  must all be subformulae of f
     * @return
     *  w: conversion result of specialSubformulae,
     *  x: a corresponding purely propositional formula/Boolean circuit
     *  y: a mapping from indefinite coefficients to the corresponding tuples
     *     of subformulae of the formula/circuit
     *  z: a mapping of prop. vars of f to the corresponding vars of x
     */
    public Quadruple<Map<Formula<Diophantine>, Formula<None>>, Formula<None>, Map<String, PolyCircuit>, Map<Variable<Diophantine>, Variable<None>>> convert(Formula<Diophantine> f,
        Collection<Formula<Diophantine>> specialSubformulae,
        Abortion aborter) throws AbortionException;


    /**
     * Converts a set of SimplePolyConstraints to be
     * fulfilled as such to a propositional
     * formula/circuit. In case there is a model for
     * the result, its interpretation of these variables
     * can be used to derive values for the indefinite
     * coefficients of <code>spcs</code> such that all
     * constraints in <code>spcs</code> are satisfied.
     *
     * This method is good for multiple calls, and it does
     * not expect its result to be on top level of the formula
     * that will be fed to the SAT solver.
     *
     * But:
     * Does not include constraints to make sure that the ranges
     * are respected in case they are not of the shape 2^k - 1.
     * Thus, you should getRangeConstraints() after your last call
     * to this method and then add the result as side conjuncts.
     *
     * @param spcs the SimplePolyConstraints to encode
     * @param aborter
     * @return a corresponding propositional formula/Boolean circuit
     * @throws AbortionException
     */
    public Formula<None> convertIteratively(Set<SimplePolyConstraint> spcs,
            Abortion aborter) throws AbortionException;

    /**
     * @param a - a Diophantine variable
     * @return which range is used for <code>a</code>
     */
    public BigInteger getRange(String a);

    /**
     * @return a DefaultValueMap which reflects which ranges are used by this;
     *  may be modified
     */
    public DefaultValueMap<String, BigInteger> getRanges();

    /**
     * Explicitly sets the range for <code>a</code> to <code>newRange</code>
     * (if possible).
     *
     * @param a - a Diophantine variable
     * @param newRange - the new range (i.e., maximum allowed value)
     *  of the Diophantine variable a
     */
    public void putRange(String a, BigInteger newRange);


    /**
     * Sets a new set of Ranges for this converter in IntegerInterval form.
     */
    public void setNewRanges(Map<String, BigIntegerInterval> newRanges);

    /**
     * Converts a single Diophantine expression. Usually has side effects on
     * the internal state of this (e.g., on the mapping of Diophantine
     * variables to formulae).
     *
     * @param dio - the atomic Diophantine proposition to be converted
     * @param aborter
     * @return a corresponding purely propositional formula
     */
    public Formula<None> convertDiophantine(Diophantine dio);

    public FormulaFactory<Diophantine> getDioFactory();
    public FormulaFactory<None> getPropFactory();


    /**
     * Get the configuration for the converter
     * @return
     */
    public PoloSatConfigInfo getConfig();


    /**
     * Interesting for assertions.
     *
     * @return whether tracking is used for the max values a poly can take
     */
    public boolean getTracking();

    /**
     * @return the binarizer used for converting Diophantine variables to
     *  PolyCircuits
     */
    public IndefiniteConverter<String> getBinarizer();
}
