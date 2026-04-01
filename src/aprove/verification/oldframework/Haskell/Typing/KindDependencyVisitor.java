package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Utility.Graph.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This visitor collects the dependencies between type declarations, class declarations
 * and type synonyms in a Graph.
 *
 */
public class KindDependencyVisitor extends DependencyVisitor {
    Set <HaskellEntity.Sort> ENTITIES = EnumSet.of(HaskellEntity.Sort.TYCLASS,
                                  HaskellEntity.Sort.INST,
                                  HaskellEntity.Sort.TYCONS);
    Set<HaskellEntity> tySyns;
    Set<HaskellEntity> filter;

    public KindDependencyVisitor(Set<HaskellEntity> filter){
        super(EnumSet.of(HaskellEntity.Sort.TYCLASS,
                         HaskellEntity.Sort.TYCONS,
             HaskellEntity.Sort.INST,
                         HaskellEntity.Sort.CONS));
        this.tySyns = new HashSet<HaskellEntity>();
    this.filter  = filter;
    }

    /**
     * The methode checks the type synonyms for recursive dependencies.
     * A HaskellError is throw if type synonyms are directly mutual dependent.
     */
    public void checkSyns(){
        HaskellDepGraph dg = new HaskellDepGraph(this.tySyns,this.depGraph);
        for (Cycle<HaskellEntity> syCy : dg.getSCCs()){
            if (syCy.size() > 1) {
               Set<HaskellEntity> cycle = syCy.getNodeObjects();
               String restext = "";
               for (HaskellEntity e : cycle){
                   restext = restext + " "+ e.getName();
               }
               HaskellError.output(cycle.iterator().next().getValue(),"Type synonymes are mutual recursive"+restext);
            }
            Node<HaskellEntity> syNode = syCy.iterator().next();
            if (this.depGraph.contains(syNode,syNode)) {
               HaskellError.output(syNode.getObject().getValue(),"Type synonyme is recursive");
            }
        }
        // pro SynTypeEntity a new group
    }

    @Override
    public List<Set<HaskellEntity>> buildGroups(){
        this.checkSyns();
        for(HaskellEntity synTy : this.tySyns) {
            this.depGraph.addEdge(synTy, synTy);
        }
        return super.buildGroups();
    }

    @Override
    public void fcaseEntity(HaskellEntity e){
        if (this.ENTITIES.contains(e.getSort())) {
            if (e.getModule().isAccessible()) {
                if (e instanceof TySynEntity) {
                    this.tySyns.add(e);
                } else {

                    if (!this.filter.contains(e)) {
                    this.depGraph.addNode(e);
                    this.depGraph.addEdge(e,e);
                    }
                }
                HaskellEntity cur = this.entityStack.peek();
                if (cur != null) {
                    if (this.ENTITIES.contains(cur.getSort())) {
                        this.depGraph.addEdge(cur, e);
                    }
                }
            }
            super.fcaseEntity(e);
        }
    }

    @Override
    public HaskellObject caseEntity(HaskellEntity e){
        if (this.ENTITIES.contains(e.getSort())) {
            return super.caseEntity(e);
        }
        return e;
    }

    @Override
    public boolean guardValue(HaskellEntity ho){
        return true;
    }

    @Override
    public boolean guardType(HaskellEntity ho){
        return (ho.getSort() == HaskellEntity.Sort.CONS);
    }

    @Override
    public boolean guardMember(HaskellEntity ho){
        return (ho.getSort() != HaskellEntity.Sort.TYCONS);
    }

    @Override
    public boolean guardHaskellNamedSym(HaskellNamedSym ho) {
        return true;
    }

    @Override
    public boolean guardDefType(SynTypeDecl ho) {
        return false;
    }

    @Override
    public boolean guardConss(DataDecl ho) {
        return true;
    }

    @Override
    public boolean guardDataConTypes(DataCon ho) {
        return true;
    }

}
