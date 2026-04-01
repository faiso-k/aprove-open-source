package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * This visitor is no longer in use...
 *
 * @author Stephan Swiderski
 * @version $Id$
 */
public class TypeDependencyVisitor extends DependencyVisitor {
    Set <HaskellEntity.Sort> VALUESOF = EnumSet.of(HaskellEntity.Sort.VAR,
                                                   HaskellEntity.Sort.IVAR,
                                                   HaskellEntity.Sort.PATDECL);
    public TypeDependencyVisitor(){
        super(EnumSet.of(HaskellEntity.Sort.TYCLASS,
                         HaskellEntity.Sort.INST,
                         HaskellEntity.Sort.VAR,
                         HaskellEntity.Sort.IVAR,
                         HaskellEntity.Sort.PATDECL
                         ));
    }

    @Override
    public void fcaseEntity(HaskellEntity e){
        if (this.VALUESOF.contains(e.getSort())) {
            HaskellEntity cur = this.entityStack.peek();
            if (cur != null) {
                if (this.VALUESOF.contains(cur.getSort()) && (e.getType() == null)) {
                    // XXX DEBUG
                    if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                        System.out.println("Adding edge "+cur+" -> "+e);
                    }

                    this.depGraph.addEdge(cur, e);
                }
            }
            this.depGraph.addNode(e);
            this.depGraph.addEdge(e,e);
        }
        super.fcaseEntity(e);
    }

    @Override
    public boolean guardValue(HaskellEntity ho){
        return this.VALUESOF.contains(ho.getSort());
    }

    @Override
    public boolean guardType(HaskellEntity ho){
        return false;
    }

    @Override
    public boolean guardMember(HaskellEntity ho){
        return true;
    }

    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) {
        return true;
    }

    @Override
    public boolean guardTypeTypeExp(TypeExp ho) {
        return false;
    }

    @Override
    public boolean guardArguments(HaskellRule ho){
        return false;
    }

}
