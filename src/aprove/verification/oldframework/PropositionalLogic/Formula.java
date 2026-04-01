package aprove.verification.oldframework.PropositionalLogic;

import java.util.*;

import aprove.GlobalSettings.SATViewSerialize;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

/**
 * To be implemented by all propositional formulae.
 *
 * Note that implementors should not override equals() and hashCode()!
 * This allows using == instead of equals, thus leading to fast comparisons.
 *
 * @author Carsten Fuhs
 *
 * @param T - common type of the TheoryAtoms (set to None if you only intend to
 *  use Boolean propositions)
 */
public interface Formula<T> extends SATViewSerialize {
    /**
     * @return whether this is a propositional atom (constant or variable)
     */
    public boolean isAtomic();

    /**
     * @return whether this is a variable
     */
    public boolean isVariable();

    /**
     * @return whether this is a TheoryAtom
     */
    public boolean isTheoryAtom();

    /**
     * @return whether this is a constant
     */
    public boolean isConstant();

    /**
     * @return whether this is a literal, i.e., a variable or a
     *  negation of a variable
     */
    public boolean isLiteral();

    /**
     * Labels *this junctor* with the provided id. Does not label any children. id can be negative.
     * @param id
     */
    public void labelThisWith(int id);

    /**
     * @return the id of this, value AbstractFormula.ID_UNSET
     *  indicates an unset id
     */
    public int getId();

    /**
     * Labels this and all unlabeled subformulae of this.
     *
     * Assumes that if this has already been labeled, then so have all
     * subformulae of this.
     *
     * (Note that in the implementation, it is advisable to pursue a post-order
     * depth-first tree/DAG run through the formula/circuit such that the
     * labeling starts at the leaves of the formula/circuit. Like this, you
     * can rest assured that if a node n has already been labeled, then so will
     * all its subformulae.)
     *
     * For incremental searches, we insist on the root of the formula having the highest label.
     *
     * The labeling will label both with an id and also with a
     * corresponding CircuitGate.
     *
     * @param newId the smallest id number to be assigned
     * @return the next id number that has not yet been assigned by the
     *  labeling method
     */
    public int label(int newId);

    /**
     * Throws an UnsupportedOperationException if called on a Variable or
     * a TheoryAtom, otherwise the gate type of the formula is returned.
     *
     * @return the corresponding gate type of the formula
     */
    public int getGateType();

    /**
     * Add the gates that describe this to <code>gates</code>.
     *
     * @param gates here all the gates that describe this are added,
     *  if you use an array based list, it had better have enough
     *  space available if you want to avoid all those costly arraycopy
     *  calls.
     */
    public void addGates(List<CircuitGate> gates);

    /**
     * Print the formula and replace all variables in the key set
     * of map by the result of the corresponding value's toString()
     * @param map Mapping from variable to whatever
     * @return hopefully human-readable String representation
     */
    public String toString(Map<? extends AbstractVariable<T>, ?> map);

    /**
     * Instantiate variables whose values are known by ONE or ZERO
     * and rebuild formula. If the formula factory supports
     * simplification the result will not contain any ONEs or
     * ZEROs.
     * @param cache Mapping from variables to truth values
     * @return evaluated formula
     */
    Formula<T> evaluate(ValueCache<T> cache);

    /**
     * Interpret this formula based on trueVars, which contains IDs of
     * those variables that are assigned to "true".
     *
     * Related to Formula.evaluate(ValueCache<T>), but works on ID level
     * rather than Java Variable object level. Only applicable to formulae
     * without TheoryAtom instances, such as Formula<None>.
     *
     * Only makes sense after Formula.label(int) has been called on
     * this formula (in particular, this is the case after SAT solving
     * was performed on the formula).
     *
     * Not necessarily very efficient. Shared subformulas may be interpreted
     * multiple times in the current interpretation. (Not problematic in
     * practice for "small" formulas as used e.g. as representatives for bits
     * of finite-domain variables on exotic (arctic or tropical) semi-rings.)
     * May use "short-circuit" evaluation -- e.g. to know about "x or y" when
     * x becomes true, there is no need to look at y.
     *
     * @param trueVars The IDs of variables (and possibly also composite
     *  subformulae) that are assigned the truth value "true".
     * @return whether this formula is true under the given model
     */
    boolean interpret(Set<Integer> trueVars);

    /**
     * Extract a variable interpretation from this formula.
     * If unsure, do not assume this does what you think it might.
     */
    void update(ValueCache<T> cache, boolean one);

    /**
     * If you are lazy, use the DepthFirstFormulaVisitor ...
     *
     * @param S - generic result type
     * @param visitor
     * @return an object of some type S
     */
    public <S> S apply(FormulaVisitor<S, T> visitor);

    /**
     * @param S - generic result type
     * @param visitor
     * @return an object of some type S
     */
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor);

    public int countSub();
}
