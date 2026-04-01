package aprove.input.Programs.llvm.internalStructures.expressions.relations;

/**
 * Produces LLVMRelations.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMDefaultRelationFactory extends LLVMRelationFactory {

    /**
     * The default factory.
     */
    public static LLVMDefaultRelationFactory LLVM_DEFAULT_RELATION_FACTORY = new LLVMDefaultRelationFactory();

    /**
     * No instances from outside.
     */
    private LLVMDefaultRelationFactory() {
        // do not instantiate me
    }

}
