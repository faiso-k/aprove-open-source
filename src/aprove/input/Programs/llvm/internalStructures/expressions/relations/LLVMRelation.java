package aprove.input.Programs.llvm.internalStructures.expressions.relations;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A Relation models dependencies between two OpNodes.
 * @author Janine Repke, cryingshadow
 */
public class LLVMRelation extends PlainIntegerRelation implements TRSTermExpressible {

    /**
     * @param map Some map between LLVMTerms.
     * @param factory A factory to build relations.
     * @return A set of relations representing equations between the mappings in the specified map.
     */
    public static Set<LLVMRelation> toSetOfEquations(
        Map<? extends LLVMTerm, ? extends LLVMTerm> map,
        LLVMRelationFactory factory
    ) {
        Set<LLVMRelation> res = new LinkedHashSet<LLVMRelation>();
        for (Map.Entry<? extends LLVMTerm, ? extends LLVMTerm> entry : map.entrySet()) {
            res.add(factory.equalTo(entry.getKey(), entry.getValue()));
        }
        return res;
    }

//    /**
//     * Checks whether phi follows from psi.
//     * Does Psi |= phi hold?
//     * @param psi A formula.
//     * @param phi Another formula.
//     * @return Yes, no, or maybe.
//     */
//    public static YNM checkImplication(Formula<SMTLIBTheoryAtom> psi, Formula<SMTLIBTheoryAtom> phi) {
//        FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
//        try {
//            // is psi => phi satisfiable?, same like psi & !psi unsatisfiable
//            return (YNM) new YicesEngine().satisfiable(
//                Collections.singletonList(factory.buildAnd(psi, factory.buildNot(phi))),
//                SMTLogic.QF_LIA,
//                AbortionFactory.create()).not();
//        } catch (AbortionException | WrongLogicException e) {
//            return YNM.MAYBE;
//        }
//    }

//    /**
//     * Creates from a given relation set an SMT formula.
//     * @param relations The relations.
//     * @return An SMT formula representing the conjunction of the specified relations.
//     */
//    public static Formula<SMTLIBTheoryAtom> createSMTFormula(Set<LLVMRelation> relations) {
//        List<SMTLIBTheoryAtom> smtList = new LinkedList<SMTLIBTheoryAtom>();
//        for (LLVMRelation relation : relations) {
//            smtList.add(relation.toSMTAtom());
//        }
//        FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
//        return factory.buildAnd(factory.buildTheoryAtoms(smtList));
//    }

    /**
     * Convenience constructor for sub-classes to initialize the parameters passed to the super call.
     * @param triple The parameters for the constructor as one object.
     */
    protected LLVMRelation(Triple<IntegerRelationType, LLVMTerm, LLVMTerm> triple) {
        this(triple.x, triple.y, triple.z);
    }

    /**
     * Should not be used outside of factory methods (this is why it is package private).
     * @param relType The type of the relation.
     * @param left The left-hand side of the relation.
     * @param right The right-hand side of the relation.
     */
    LLVMRelation(IntegerRelationType relType, LLVMTerm left, LLVMTerm right) {
        super(relType, left, right);
    }

    @Override
    public LLVMRelation applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    public LLVMRelation applySubstitution(Substitution sigma) {
        return Substitution.applySubstitution(this, sigma);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        LLVMRelation other = (LLVMRelation)obj;
        if (this.getRelationType() != other.getRelationType()) {
            return false;
        }
        switch (this.getRelationType()) {
            case EQ:
            case NE:
                return
                    (this.getLhs().equals(other.getLhs()) && this.getRhs().equals(other.getRhs()))
                    || (this.getLhs().equals(other.getRhs()) && this.getRhs().equals(other.getLhs()));
            default:
                return this.getLhs().equals(other.getLhs()) && this.getRhs().equals(other.getRhs());
        }
    }

    @Override
    public LLVMTerm getLhs() {
        return (LLVMTerm)super.getLhs();
    }

    @Override
    public LLVMTerm getRhs() {
        return (LLVMTerm)super.getRhs();
    }

//    /**
//     * If this method returns true, we can then get the relation through
//     * this.getStrictestSubsumingRelation(other).
//     * @param other Some other Relation
//     * @return True iff we can represent some relation ret such that
//     * (this || other) ==> ret.
//     */
//    public boolean canRepresentStrictestSubsumingRelation(final LLVMRelation other) {
//        final boolean verbatimEqual = this.lhs.equals(other.lhs) && this.rhs.equals(other.rhs);
//        final boolean mirroredEqual = this.lhs.equals(other.rhs) && this.rhs.equals(other.lhs);
//        final boolean isSymmetrical = this.type.isSymmetrical() || other.type.isSymmetrical();
//
//        final boolean compatibleSides = (verbatimEqual || (isSymmetrical && mirroredEqual));
//
//        if (compatibleSides) {
//            final boolean canRepresentSubsumingType = (this.type.merge(other.type) != null);
//            return canRepresentSubsumingType;
//        } else {
//            return false;
//        }
//    }

    @Override
    @SuppressWarnings("unchecked")
    public Set<? extends LLVMSymbolicVariable> getVariables() {
        return (Set<? extends LLVMSymbolicVariable>)super.getVariables();
    }

    @Override
    public int hashCode() {
        int prime = 37;
        int result = 1;
        result =
            prime * result
            + ((this.getLhs() == null) ? 0 : this.getLhs().hashCode())
            + ((this.getRhs() == null) ? 0 : this.getRhs().hashCode());
        result = prime * result + ((this.getRelationType() == null) ? 0 : this.getRelationType().ordinal());
        return result;
    }

    @Override
    public LLVMRelation negate() {
        return this.getRelationFactory().createRelation(this.getRelationType().invert(), this.getLhs(), this.getRhs());
    }

    @Override
    public LLVMRelation setLhs(FunctionalIntegerExpression lhs) {
        return this.setLhs((LLVMTerm)lhs);
    }

    /**
     * @param left The new left-hand side.
     * @return A relation with the specified left-hand side and the current right-hand side.
     */
    public LLVMRelation setLhs(LLVMTerm left) {
        return this.getRelationFactory().createRelation(this.getRelationType(), left, this.getRhs());
    }

    @Override
    public LLVMRelation setRhs(FunctionalIntegerExpression rhs) {
        return this.setRhs((LLVMTerm)rhs);
    }

//    /**
//     * @return an SMTLIB atom corresponding to the encoded integer information.
//     */
//    public SMTLIBTheoryAtom toSMTAtom() {
//        SMTLIBIntValue leftValue = this.getLhs().toSMTIntValue();
//        SMTLIBIntValue rightValue = this.getRhs().toSMTIntValue();
//        if (leftValue == null || rightValue == null) {
//            return SMTLIBBoolTrue.create();
//        }
//        switch (this.type) {
//        case LT:
//            return SMTLIBIntLT.create(leftValue, rightValue);
//        case LE:
//            return SMTLIBIntLE.create(leftValue, rightValue);
//        case EQ:
//            return SMTLIBIntEquals.create(leftValue, rightValue);
//        case NE:
//            return SMTLIBIntUnequal.create(leftValue, rightValue);
//        default:
//            throw new IllegalStateException("Unknown relation type");
//        }
//    }

    /**
     * @param right The new right-hand side.
     * @return A relation with the current left-hand side and the specified right-hand side.
     */
    public LLVMRelation setRhs(LLVMTerm right) {
        return this.getRelationFactory().createRelation(this.getRelationType(), this.getLhs(), right);
    }

//    /**
//     * Creates a SMT-formula of the relation.
//     * @return The SMT-formula.
//     */
//    public Formula<SMTLIBTheoryAtom> toSMTFormula() {
//        return this.toSMTFormula(new AtomCachingFactory<SMTLIBTheoryAtom>());
//    }

//    /**
//     * Creates a SMT-formula of the relation.
//     * @param factory The formula factory.
//     * @return The SMT-formula.
//     */
//    public Formula<SMTLIBTheoryAtom> toSMTFormula(FormulaFactory<SMTLIBTheoryAtom> factory) {
//        return factory.buildTheoryAtom(this.toSMTAtom());
//    }

    @Override
    public String toJSON() {
        return this.toSExpressionString();
    }

    @Override
    public String toString() {
        return this.toPrettyString();
    }

    @Override
    public TRSTerm toTerm() {
        TRSTerm lhsTerm = this.getLhs().toTerm();
        TRSTerm rhsTerm = this.getRhs().toTerm();
        FunctionSymbol relationSymbol;
        switch (this.getRelationType()) {
            case GT:
                relationSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Gt, DomainFactory.INTEGER_INTEGER);
                break;
            case GE:
                relationSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Ge, DomainFactory.INTEGER_INTEGER);
                break;
            case LT:
                relationSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Lt, DomainFactory.INTEGER_INTEGER);
                break;
            case LE:
                relationSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Le, DomainFactory.INTEGER_INTEGER);
                break;
            case EQ:
                relationSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Eq, DomainFactory.INTEGER_INTEGER);
                break;
            case NE:
                relationSymbol = IDPPredefinedMap.DEFAULT_MAP.getSym(Func.Neq, DomainFactory.INTEGER_INTEGER);
                break;
            default:
                throw new IllegalStateException("There are no other relation types!");
        }
        return TRSTerm.createFunctionApplication(relationSymbol, lhsTerm, rhsTerm);
    }

    /**
     * @return The factory to build new relations.
     */
    protected LLVMRelationFactory getRelationFactory() {
        return LLVMDefaultRelationFactory.LLVM_DEFAULT_RELATION_FACTORY;
    }

    /**
     * @return The factory to build terms.
     */
    protected LLVMTermFactory getTermFactory() {
        return this.getRelationFactory().getTermFactory();
    }

}
