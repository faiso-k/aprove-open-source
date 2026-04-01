package aprove.verification.oldframework.Haskell.Typing;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This Visitor collects all relevant informations of the class hierachy
 * and save it into the given constraint graph
 */
public class ClassConstraintVisitor extends HaskellVisitor {
    ClassConstraintGraph ccg;

    public ClassConstraintVisitor(ClassConstraintGraph ccg){
        this.ccg = ccg;
    }

    @Override
    public void fcaseEntity(HaskellEntity ho){
        if (ho.getSort()== HaskellEntity.Sort.INST) {
            // the head of instance declaration is saved in the rule set
            this.ccg.addRule(((InstEntity)ho).getConstraintRule());
        }
        if (ho.getSort()== HaskellEntity.Sort.TYCLASS) {
           if (ho.getName().equals("Num")) {
              // the num class is saved extra for default-rule
              if (ho.getModule().isPrelude()) {
                 this.ccg.setNumTyClass(ho);
              }
           }
           // save the head of a class-Declaration as new node and edge structure
           // in the ClassConstraintGraph (the class hierachy)
           ClassConstraintRule ccr = ((TyClassEntity)ho).getConstraintRule();
           this.ccg.checkForSimpleConstraints(ccr.getResults(),ho);
           ccr.addEdgesTo(this.ccg);
        }
    }

    @Override
    public boolean guardValue(HaskellEntity ho){
        return false;
    }
    @Override
    public boolean guardEntity(HaskellEntity ho){
        return false;
    }

    @Override
    public boolean guardType(HaskellEntity ho){
        return false;
    }

    @Override
    public boolean guardMember(HaskellEntity ho){
        return false;
    }

    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) {
        return false;
    }

    @Override
    public boolean guardConss(DataDecl ho){
        return false;
    }

    @Override
    public boolean guardDefType(SynTypeDecl ho){
        return false;
    }

    @Override
    public boolean guardDecls(TTDecl ho){
        return false;
    }

}
