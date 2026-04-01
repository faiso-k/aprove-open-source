package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Collectors.*;


/**
 * the TypeAnnotationVarSymCollector collects all va-Symbols
 * of the type annotation of the visited HaskellObject
 * and stores them in the given collection
 */
public class TypeAnnotationVarSymCollector extends HaskellVisitor {
    FreeVarSymCollector fvsc;

    public TypeAnnotationVarSymCollector(Collection<HaskellSym> varSyms) {
        this.fvsc = new FreeVarSymCollector(varSyms);
    }

    @Override
    public void fcaseAll(HaskellObject ho){
        HaskellType type = ho.getTypeTerm();
        if (type != null) {
            type.visit(this.fvsc);
        }
    }

    public void applyTo(HaskellObject ho){
        this.fcaseAll(ho);
        ho.visit(this);
    }
}
