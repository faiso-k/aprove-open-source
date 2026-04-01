package aprove.verification.oldframework.Haskell.Typing;

import aprove.verification.oldframework.Haskell.*;

/**
 * the TypeAnnotationSubstitutor applies a type-substitution to all type-annotations
 * of the visited HaskellObject
 */

public class TypeAnnotationSubstitutor extends HaskellVisitor {
    HaskellSubstitution tsubs;

    public TypeAnnotationSubstitutor(HaskellSubstitution tsubs) {
        this.tsubs = tsubs;
    }

    @Override
    public void fcaseAll(HaskellObject ho){
        HaskellType type = ho.getTypeTerm();
        if (type != null) {
            ho.setTypeTerm((HaskellType)this.tsubs.applyToDestructive(type));
        }
    }

    public void applyTo(HaskellObject ho){
        this.fcaseAll(ho);
        ho.visit(this);
    }
}
