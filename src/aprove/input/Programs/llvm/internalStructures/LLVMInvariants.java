package aprove.input.Programs.llvm.internalStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.segraph.edges.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;

/**
 * Modes for adding invariants to IRSs from instance edges.
 * @author cryingshadow
 * @version $Id$
 */
public enum LLVMInvariants {

    /**
     * All relations in a state are added to the condition of the corresponding edge.
     */
    ALL {

        @Override
        public TRSTerm getCondition(LLVMAbstractState from, LLVMAbstractState to, LLVMEdgeInformation info) {
            return LLVMRelationUtils.toTerm(to.getInvariants());
        }

    },

    /**
     * All directed inequalities that do not exist as equations in a state are added to the condition of the
     * corresponding edge.
     */
    BOUNDS {

        @Override
        public TRSTerm getCondition(LLVMAbstractState from, LLVMAbstractState to, LLVMEdgeInformation info) {
            final Set<LLVMRelation> invariants = new LinkedHashSet<LLVMRelation>();
            final Set<LLVMRelation> equations = new LinkedHashSet<LLVMRelation>();
            for (LLVMRelation rel : to.getInvariants()) {
                if (rel.isDirectedInequality()) {
                    invariants.add(rel);
                } else if (rel.isEquation()) {
                    equations.add(rel);
                }
            }
            final Iterator<LLVMRelation> it = invariants.iterator();
            while (it.hasNext()) {
                final LLVMRelation rel = it.next();
                final LLVMTerm lhs = rel.getLhs();
                final LLVMTerm rhs = rel.getRhs();
                for (LLVMRelation eq : equations) {
                    if (
                        (eq.getLhs().equals(lhs) && eq.getRhs().equals(rhs))
                        || (eq.getLhs().equals(rhs) && eq.getRhs().equals(lhs))
                    ) {
                        it.remove();
                    }
                }
            }
            return LLVMRelationUtils.toTerm(invariants);
        }

    },

    /**
     * The relations stored on the edge are added to the condition of the corresponding edge.
     */
    CHANGES {

        @Override
        public TRSTerm getCondition(LLVMAbstractState from, LLVMAbstractState to, LLVMEdgeInformation info) {
            return info.toTerm();
        }

    },

    /**
     * The relations stored on the edge are added to the condition of the corresponding edge. For instance edges,
     * all directed inequalities that do not exist as equations in the state are added to the condition of the
     * corresponding edge.
     */
    CHANGESANDINSTBOUNDS {

        @Override
        public TRSTerm getCondition(LLVMAbstractState from, LLVMAbstractState to, LLVMEdgeInformation info) {
            if (info instanceof LLVMInstantiationInformation) {
                return BOUNDS.getCondition(from, to, info);
            } else {
                return CHANGES.getCondition(from, to, info);
            }
        }

    },

    /**
     * The relations stored on the edge are added to the condition of the corresponding edge.
     */
    CHANGESANDINSTNONE {

        @Override
        public TRSTerm getCondition(LLVMAbstractState from, LLVMAbstractState to, LLVMEdgeInformation info) {
            if (info instanceof LLVMInstantiationInformation) {
                return NONE.getCondition(from, to, info);
            } else {
                return CHANGES.getCondition(from, to, info);
            }
        }

    },

    /**
     * The condition for the corresponding edge is always TRUE.
     */
    NONE {

        @Override
        public TRSTerm getCondition(LLVMAbstractState from, LLVMAbstractState to, LLVMEdgeInformation info) {
            return TRSTerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.getBooleanTrue().getSym());
        }

    };

    /**
     * @param from The start state of the edge.
     * @param to The end state of the edge.
     * @param info The edge label.
     * @return The condition term for the corresponding IRS rule.
     */
    public abstract TRSTerm getCondition(LLVMAbstractState from, LLVMAbstractState to, LLVMEdgeInformation info);

}
