/**
 * @version $Id$
 */

package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import immutables.*;

/**
 * A boolean formula with instances of T as literals.
 *
 *  @author noschinski
 */
public final class ImmutableBoolOp<T> {

    /**
     * Boolean connectives
     */
    public static enum Op { atom, and, or, not }

    /** The kind of boolean operation */
    protected final Op op;

    /**
     * Only if this.op != Op.atom: The list of operands of this
     * operation */
    protected final ImmutableList<ImmutableBoolOp<T>> subformulas;

    /**
     * Only if this.op == Op.atom: The literal.
     */
    protected final T variable;

    public static final int EXPAND_INFINITE = -1;

    private ImmutableBoolOp(T var) {
        this.op = Op.atom;
        this.variable = var;
        this.subformulas = null;
    }

    private ImmutableBoolOp(Op op, ImmutableList<ImmutableBoolOp<T>> c) {
        /* op may not be Op.atom. This is ensured statically , as this
         * method can only be called by createConjunction and
         * createDisjunction */
        this.op = op;
        this.variable = null;
        this.subformulas = ImmutableCreator.create(c);
    }

    /** Creates a new BoolOp consisting of the literal var. */
    public static <T> ImmutableBoolOp<T> createAtom(T var) {
        return new ImmutableBoolOp<T>(var);
    }

    /** Creates a new BoolOp describing the conjunction of the formulas in c. */
    public static <T> ImmutableBoolOp<T> createConjunction(List<ImmutableBoolOp<T>> c) {
        return new ImmutableBoolOp<T>(Op.and, ImmutableCreator.create(c));
    }

    /** Creates a new BoolOp describing the conjunction of b1, b2 */
    public static <T> ImmutableBoolOp<T> createConjunction(ImmutableBoolOp<T> b1, ImmutableBoolOp<T> b2) {
        List<ImmutableBoolOp<T>> c = new ArrayList<ImmutableBoolOp<T>>(2);
        c.add(b1);
        c.add(b2);
        return new ImmutableBoolOp<T>(Op.and, ImmutableCreator.create(c));
    }

    /** Creates a new BoolOp describing the disjunction of the formulas in c. */
    public static <T> ImmutableBoolOp<T> createDisjunction(List<ImmutableBoolOp<T>> c) {
        return new ImmutableBoolOp<T>(Op.or, ImmutableCreator.create(c));
    }

    /** Creates a new BoolOp describing the disjunction of b1, b2. */
    public static <T> ImmutableBoolOp<T> createDisjunction(ImmutableBoolOp<T> b1, ImmutableBoolOp<T> b2) {
        List<ImmutableBoolOp<T>> c = new ArrayList<ImmutableBoolOp<T>>(2);
        c.add(b1);
        c.add(b2);
        return new ImmutableBoolOp<T>(Op.or, ImmutableCreator.create(c));
    }

    /**
     * Creates a new BoolOp describing the negation of b.
     *
     * A negation has always exactly one subformula. */
    public static <T> ImmutableBoolOp<T> createNegation(ImmutableBoolOp<T> b) {
        List<ImmutableBoolOp<T>> c = new ArrayList<ImmutableBoolOp<T>>(1);
        c.add(b);
        return new ImmutableBoolOp<T>(Op.not, ImmutableCreator.create(c));
    }

    /** Creates a new BoolOp describing "False".
     *
     *  "False" is represented by an empty disjunction. */
    public static <T> ImmutableBoolOp<T> createFalse() {
        ImmutableList<ImmutableBoolOp<T>> emptyList =
            ImmutableCreator.create(new ArrayList<ImmutableBoolOp<T>>(0));
        return new ImmutableBoolOp<T>(Op.or, emptyList);
    }

    /** Creates a new BoolOp describing "True"
     *
     * "True" is represented by an empty conjunction. */
    public static <T> ImmutableBoolOp<T> createTrue() {
        ImmutableList<ImmutableBoolOp<T>> emptyList =
            ImmutableCreator.create(new ArrayList<ImmutableBoolOp<T>>(0));
        return new ImmutableBoolOp<T>(Op.and, emptyList);
    }

    /** Checks if this formula is an Atom */
    public boolean isAtom() {
        return this.op == Op.atom;
    }

    /** Checks if this formula is a Conjunction*/
    public boolean isConjunction() {
        return this.op == Op.and;
    }

    /** Checks if this formula is a Disjunction */
    public boolean isDisjunction() {
        return this.op == Op.or;
    }

    /** Checks if this formula is a Negation */
    public boolean isNegation() {
        return this.op == Op.not;
    }

    /** Checks if this formula is a True constant.
     *
     * This does not check if this formula is a tautology! */
    public boolean isObviouslyTrue() {
        return this.isConjunction() && this.subformulas.isEmpty();
    }

    /** Checks if this formula is a False constant.
     *
     * This does not check if this formula is a contradiction! */
    public boolean isObviouslyFalse() {
        return this.isDisjunction() && this.subformulas.isEmpty();
    }

    /** Checks if this formula is a True or False constant.
     *
     * This does not check if this formula is a tautology or contradiction! */
    public boolean isTrivial() {
         return !this.isAtom() && this.subformulas.isEmpty();
     }

    /** The literal in an Atom.
     *
     * Only meaningful if this.isAtom() is true.
     */
    public T getLiteral() {
        return this.variable;
    }

    /** The collection of Subformulas.
     *
     * Only meaningful if this.isAtom() is false.
     */
    public ImmutableList<ImmutableBoolOp<T>> getSubformulas() {
        return this.subformulas;
    }

    public void visit(ImmutableBoolOpVisitor<T> v) {
        switch(this.op) {
            case and:
                if (this.subformulas.isEmpty()) {
                    v.inTrue();
                } else {
                    v.inConjunction(this.subformulas);
                    boolean first = true;
                    for (ImmutableBoolOp<T> sf : this.subformulas) {
                        if (first) {
                            first = false;
                        } else {
                            v.midConjunction(this.subformulas);
                        }
                        v.apply(sf);
                    }
                    v.outConjunction(this.subformulas);
                }
                break;

            case atom:
                v.inAtom(this.variable);
                break;

            case not:
                {
                    ImmutableBoolOp<T> sf = this.subformulas.get(0);
                    v.inNegation(sf);
                    v.apply(sf);
                    v.outNegation(sf);
                }
                break;

            case or:
                if (this.subformulas.isEmpty()) {
                    v.inFalse();
                } else {
                    v.inDisjunction(this.subformulas);
                    boolean first = true;
                    for (ImmutableBoolOp<T> sf : this.subformulas) {
                        if (first) {
                            first = false;
                        } else {
                            v.midDisjunction(this.subformulas);
                        }
                        v.apply(sf);
                    }
                    v.outDisjunction(this.subformulas);
                }
                break;
        }

    }

}
