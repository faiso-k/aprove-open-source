package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;


/**
 * the TypeAnnotationCollector collects all type-annotation
 * of the visited HaskellObject and stores them in a given collection
 */
public class TypeAnnotationCollector extends HaskellVisitor {
    Collection<HaskellObject> typeAnnos;

    public TypeAnnotationCollector(Collection<HaskellObject> typeAnnos) {
        this.typeAnnos = typeAnnos;
    }

    @Override
    public void fcaseAll(HaskellObject ho){
        HaskellType type = ho.getTypeTerm();
        if (type != null) {
            this.typeAnnos.add(type);
        }
    }

    public void applyTo(HaskellObject ho){
        this.fcaseAll(ho);
        ho.visit(this);
    }
}
