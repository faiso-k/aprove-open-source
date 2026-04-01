package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;

import org.json.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.SMT.Solver.SMTInterpol.*;
import immutables.*;

/**
 * Representation of (some) integer relations in states we consider to be
 * important.
 *
 * @author Marc Brockschmidt
 */
public class IntegerRelations implements Cloneable {
    /** The actual relations. */
    private final Set<JBCIntegerRelation> relations;

    /**
     * Creates a fresh, empty object.
     */
    public IntegerRelations() {
        this.relations = new LinkedHashSet<JBCIntegerRelation>();
    }

    /**
     * Returns a deep (!) copy of this {@link IntegerRelations} object.
     * @return Deep copy of this object
     */
    @Override
    public IntegerRelations clone() {
        final IntegerRelations clone = new IntegerRelations();
        clone.relations.addAll(this.relations);
        return clone;
    }

    /**
     * Note that newRef was created from oldRef by adding diff.
     * @param newRef some new integer reference
     * @param oldRef some existing integer reference
     * @param diff the difference between the two
     * @return @see IntegerRelations#isContradictory()
     */
    public boolean noteNewRefInRelation(final AbstractVariableReference newRef, final AbstractVariableReference oldRef, final int diff) {
        final Set<JBCIntegerRelation> newRels = new LinkedHashSet<JBCIntegerRelation>();
        if (diff > 0) {
            newRels.add(new JBCIntegerRelation(newRef, IntegerRelationType.GT, oldRef));
        } else if (diff < 0) {
            newRels.add(new JBCIntegerRelation(newRef, IntegerRelationType.LT, oldRef));
        }
        // Find all relations with oldRef:
        for (final JBCIntegerRelation intRel : this.relations) {
            final AbstractVariableReference leftRef = intRel.getLeftIntRef();
            final AbstractVariableReference rightRef = intRel.getRightIntRef();

            AbstractVariableReference otherRef = null;
            IntegerRelationType rel = null;
            if (oldRef.equals(leftRef)) {
                otherRef = rightRef;
                rel = intRel.getRelationType();
            } else if (oldRef.equals(rightRef)) {
                otherRef = leftRef;
                rel = intRel.getRelationType().mirror();
            }

            //We found a fitting relation (normalized to have the old ref on the lhs):
            if (rel != null) {
                //newRef < oldRef <= otherRef  ---> newRef < otherRef
                //newRef <= oldRef < otherRef  ---> newRef < otherRef
                if (diff < 0 && (rel == IntegerRelationType.LT || rel == IntegerRelationType.LE)) {
                    newRels.add(new JBCIntegerRelation(newRef, IntegerRelationType.LT, otherRef));

                //newRef <= oldRef <= otherRef  ---> newRef <= otherRef
                } else if (diff <= 0 && (rel == IntegerRelationType.LT || rel == IntegerRelationType.LE)) {
                    newRels.add(new JBCIntegerRelation(newRef, IntegerRelationType.LE, otherRef));

                //newRef > oldRef >= otherRef  ---> newRef > otherRef
                //newRef >= oldRef > otherRef  ---> newRef > otherRef
                } else if (diff > 0 && (rel == IntegerRelationType.GT || rel == IntegerRelationType.GE)) {
                    newRels.add(new JBCIntegerRelation(newRef, IntegerRelationType.GT, otherRef));

                //newRef >= oldRef > otherRef  ---> newRef > otherRef
                } else if (diff >= 0 && (rel == IntegerRelationType.GT || rel == IntegerRelationType.GE)) {
                    newRels.add(new JBCIntegerRelation(newRef, IntegerRelationType.GE, otherRef));

                //newRef = oldRef + 1 && oldRef < otherRef  --->  newRef <= otherRef
                } else if (diff == 1 && rel == IntegerRelationType.LT) {
                    newRels.add(new JBCIntegerRelation(newRef, IntegerRelationType.LE, otherRef));

                //newRef = oldRef - 1 && oldRef > otherRef  --->  newRef >= otherRef
                } else if (diff == -1 && rel == IntegerRelationType.GT) {
                    newRels.add(new JBCIntegerRelation(newRef, IntegerRelationType.GE, otherRef));
                }
            }
        }

        boolean contradictory = false;
        for (final JBCIntegerRelation newRel : newRels) {
            if (!newRel.getLeftIntRef().pointsToConstant() || !newRel.getRightIntRef().pointsToConstant()) {
                contradictory |= note(newRel);
            }
        }
        return contradictory;
    }

    /**
     * Note that xR rel yR holds.
     * @param xR some reference
     * @param rel some relation
     * @param yR some other reference
     * @return @see IntegerRelations#isContradictory()
     */
    public boolean note(final AbstractVariableReference xR, final IntegerRelationType rel,
            final AbstractVariableReference yR) {
        return note(new JBCIntegerRelation(xR, rel, yR));
    }

    /** @return @see IntegerRelations#isContradictory() */
    private boolean note(JBCIntegerRelation rel) {
        if (!rel.justVariables() || rel.leftEqRight() || contains(rel)) {
            return false;
        }
        relations.add(rel);
        switch (rel.getRelationType()) {
            case LT:
            case GT:
                remove(rel.toNonStrict());
                remove(rel.as(IntegerRelationType.NE));
                break;
            case EQ:
                remove(rel.as(IntegerRelationType.GE));
                remove(rel.as(IntegerRelationType.LE));
                break;
            case LE:
            case GE:
                JBCIntegerRelation toCheck = rel.as(rel.getRelationType().mirror());
                if (contains(toCheck)) {
                    remove(rel);
                    remove(toCheck);
                    note(rel.as(IntegerRelationType.EQ));
                }
                break;
            case NE:
                toCheck = rel.as(IntegerRelationType.GE);
                if (contains(toCheck)) {
                    remove(toCheck);
                    remove(rel);
                    note(rel.as(IntegerRelationType.GT));
                }
                toCheck = rel.as(IntegerRelationType.LE);
                if (contains(toCheck)) {
                    remove(toCheck);
                    remove(rel);
                    note(rel.as(IntegerRelationType.LT));
                }
                break;
            default:
                break;
        }
        return isContradictory();
    }

    private void remove(JBCIntegerRelation rel) {
        relations.remove(rel);
        relations.remove(rel.mirror());
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb);
        return sb.toString();
    }

    public void toString(final StringBuilder sb) {
        boolean first = true;
        for (final JBCIntegerRelation intRel : this.relations) {
            if (!first) {
                sb.append(", ");
            } else {
                first = false;
            }
            sb.append(intRel.toString());
        }
        sb.append('\n');
    }

    public ImmutableSet<JBCIntegerRelation> getRelations() {
        return ImmutableCreator.create(this.relations);
    }

    /**
     * @param res for each AbstractVariableReference the number of occurrences in these relations
     */
    public void getReferences(Map<AbstractVariableReference, Integer> res) {
        for (JBCIntegerRelation rel : this.getRelations()) {
            AbstractVariableReference l = rel.getLeftIntRef();
            if (l != null) {
                res.put(l, res.get(l)+1);
            }
            AbstractVariableReference r = rel.getRightIntRef();
            if (r != null) {
                res.put(r, res.get(r)+1);
            }
        }
    }

    /** @return true iff these relations imply the given one */
    public boolean implies(final JBCIntegerRelation rel) {
        SMTSolver solver = new SMTInterpolIntSolver(SMTLIBLogic.QF_LIA, AbortionFactory.create());
        List<SMTExpression<SBool>> exps = new LinkedList<>();
        for (JBCIntegerRelation r: this.relations) {
            exps.add(r.toSMTExp());
        }
        SMTExpression<SBool> premise = Symbol0.True;;
        if (!exps.isEmpty()) {
            premise = new LeftAssocCall<SBool, SBool>(LeftAssocSymbol.And, Symbol0.True, ImmutableCreator.create(exps));
        }
        SMTExpression<SBool> implication = new RightAssocCall<>(RightAssocSymbol.Implies, ImmutableCreator.create(Collections.singletonList(premise)), rel.toSMTExp());
        solver.addAssertion(new Call1<SBool, SBool>(Symbol1.Not, implication));
        YNM res = solver.checkSAT();
        switch (res) {
            case YES:
                return false;
            case NO:
                return true;
            case MAYBE:
                assert false: "This should be easily decidable!";
                return false;
            default: return false;
        }
    }

    /** @return true iff a single relation of these implies the given one */
    public boolean contains(JBCIntegerRelation rel) {
        Set<JBCIntegerRelation> toCheck = new LinkedHashSet<>();
        switch (rel.getRelationType()) {
            case NE:
                toCheck.add(rel);
                toCheck.add(rel.mirror());
                toCheck.add(rel.as(IntegerRelationType.LT));
                toCheck.add(rel.as(IntegerRelationType.LT).mirror());
                toCheck.add(rel.as(IntegerRelationType.GT));
                toCheck.add(rel.as(IntegerRelationType.GT).mirror());
                break;
            case EQ:
                toCheck.add(rel);
                toCheck.add(rel.mirror());
                break;
            default:
                toCheck.add(rel);
                toCheck.add(rel.mirror());
                if (!rel.isStrict()) {
                    toCheck.add(rel.as(IntegerRelationType.EQ));
                    toCheck.add(rel.as(IntegerRelationType.EQ).mirror());
                    toCheck.add(rel.toStrict());
                    toCheck.add(rel.mirror().toStrict());
                }
        }
        for (JBCIntegerRelation r : toCheck) {
            if (relations.contains(r)) {
                return true;
            }
        }
        return false;
    }

    public void remove(final AbstractVariableReference ref) {
        final Iterator<JBCIntegerRelation> it = this.relations.iterator();
        while (it.hasNext()) {
            final JBCIntegerRelation rel = it.next();
            if (ref.equals(rel.getLeftIntRef()) || ref.equals(rel.getRightIntRef())) {
                it.remove();
            }
        }
    }

    /**
     * removes all Integer Relations
     */
    public void clear () {
        this.relations.clear();
    }

    /**
     * @return true iff there is no known relation
     */
    public boolean isEmpty() {
        return this.relations.isEmpty();
    }

    /** @return @see IntegerRelations#isContradictory() */
    public boolean replaceReference(AbstractVariableReference oldRef, AbstractVariableReference newRef) {
        if (newRef.pointsToConstant()) {
            remove(oldRef);
            return false;
        }
        Set<JBCIntegerRelation> oldRelations = new LinkedHashSet<>(relations);
        relations.clear();
        boolean contradictory = false;
        for (JBCIntegerRelation r: oldRelations) {
            JBCIntegerRelation rel = r;
            if (oldRef.equals(r.getRightIntRef())) {
                rel = r.mirror();
            }
            if (oldRef.equals(rel.getLeftIntRef())) {
                assert !oldRef.equals(rel.getRightIntRef());
                if (rel.rightIntegerIsNoRef()) {
                    contradictory |= note(new JBCIntegerRelation(newRef, rel.getRelationType(), (LiteralInt) rel.getRightInt()));
                } else {
                    contradictory |= note(newRef, rel.getRelationType(), rel.getRightIntRef());
                }
            } else {
                contradictory |= note(r);
            }
        }
        return contradictory;
    }

    /** @return true if the set of relations is contradictory, false if we don't know */
    public boolean isContradictory() {
        for (JBCIntegerRelation rel: relations) {
            if (contains(rel.invert())) {
                return true;
            }
        }
        return false;
    }

    public JSONArray toJSON() throws JSONException {
        final JSONArray res = new JSONArray();
        for (JBCIntegerRelation rel : this.relations) {
            res.put(rel.toSExpString());
        }
        return res;
    }
}
