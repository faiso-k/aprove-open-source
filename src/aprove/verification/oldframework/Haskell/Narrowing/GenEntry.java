package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;

public class GenEntry {
    public int num;
    HaskellEntity entity;
    public List<GenMap> params;
    Set<NarrowNode> nodes;
    int depth;
    int count;
    boolean head;
    GenParameters genParameters;

    public GenEntry(HaskellEntity entity,int arity,int depth,GenParameters genParameters){
        this.num = HaskellNarrowing.ecount;
        HaskellNarrowing.ecount++;
        this.genParameters = genParameters;
        this.entity = entity;
        this.params = new Vector<GenMap>();
        this.nodes = new HashSet<NarrowNode>();
        this.count = 0;
        this.head = true;
        this.depth = depth;
        for (int i=0;i<arity;i++){
            this.params.add(new GenMap(this.depth+1,i,genParameters));
        }
    }

    @Override
    public String toString(){
        String s = "";
        for (NarrowNode node : this.nodes){
            s = s + node.num+",";
        }
        return this.entity+"/"+this.params.size()+"["+this.head+","+this.depth+","+this.count+"]{"+s+"}";
    }

    public Set<NarrowNode> getNodes(){
        return this.nodes;
    }

    public boolean removeAll(Collection<NarrowNode> rnodes){
        this.nodes.removeAll(rnodes);
        if (this.nodes.isEmpty()) {
            for (GenMap genMap : this.params){
                genMap.clear();
            }
            return true;
        }
        for (GenMap genMap : this.params){
            genMap.removeAll(rnodes);
        }
        return false;
    }

    protected GenSet ogenInsert(NarrowNode node,List<HaskellObject> exps,Stack<GenEntry> genEntries){
        this.nodes.add(node);
        Iterator<HaskellObject> it = exps.iterator();
        genEntries.push(this);
        GenSet genSet = null;
        int i=0;
        for (GenMap genMap : this.params){
            if (!it.hasNext()) {
                throw new RuntimeException("arity is different");
            }
            GenSet cGenSet = genMap.genInsert(node,it.next(),genEntries);
            if (genSet == null){
                genSet = cGenSet;
            }
            if (genSet == null) {
                i++;
            }
        }
        genEntries.pop();
        if (genSet != null) {
            if (genSet.check()){
                genSet.addPositionPrefix(i);
                int j = 0;
                for (GenMap genMap : this.params){
                    if (i != j) {
                        genSet = genMap.collectBy(genSet,node);
                    }
                    j++;
                }
                return genSet;
            }
        }
        boolean stop = (this.nodes.size()>this.genParameters.maxArgumentHeadVariants) && (this.depth > 1);
        return GenSet.checkAndStart(this.nodes,stop || (!this.head && (this.count > this.genParameters.multiNestingDepth)),stop || (this.count > this.genParameters.monoNestingDepth));
    }

    protected GenSet genInsert(NarrowNode node,List<HaskellObject> exps,Stack<GenEntry> genEntries){
        this.nodes.add(node);
        Iterator<HaskellObject> it = exps.iterator();
        genEntries.push(this);
        GenSet genSet = null;
        int i=0;
        for (GenMap genMap : this.params){
            if (!it.hasNext()) {
                throw new RuntimeException("arity is different");
            }
            GenSet cGenSet = genMap.genInsert(node,it.next(),genEntries);
            if (genSet == null){
                genSet = cGenSet;
            }
            if (genSet == null) {
                i++;
            }
        }
        genEntries.pop();
        boolean stop = (this.nodes.size()>this.genParameters.maxArgumentHeadVariants) && (this.depth > 1);
        GenSet cg = GenSet.checkAndStart(this.nodes,stop || (!this.head && (this.count > this.genParameters.multiNestingDepth)),stop || (this.count > this.genParameters.monoNestingDepth));
        if (cg != null) {
            return cg;
        }
        if (genSet != null) {
            if (genSet.check()){
                genSet.addPositionPrefix(i);
                int j = 0;
                for (GenMap genMap : this.params){
                    if (i != j) {
                        genSet = genMap.collectBy(genSet,node);
                    }
                    j++;
                }
                return genSet;
            }
        }
        return null;
    }

    protected void symCount(Stack<GenEntry> genEntries){
        this.increaseAll(genEntries);
        genEntries.push(this);
        this.count = 0;
        for (GenMap genMap : this.params){
            genMap.symCount(genEntries);
        }
        genEntries.pop();
    }

    public void increaseAll(Stack<GenEntry> genEntries){
        for (GenEntry genEntry : genEntries){
            if (genEntry.increaseFor(this)) {
                this.head = false;
            }
        }
    }

    public boolean increaseFor(GenEntry ge){
        if ((this.entity == ge.entity) && (this.params.size() == ge.params.size())) {
            this.count++;
            return true;
        }
        return false;
    }

    public GenSet collectBy(GenSet cnodes,NarrowNode current){
        GenSet rNodes = new GenSet(cnodes);
        rNodes.retainAll(this.nodes);
        for (GenMap genMap : this.params){
            rNodes = genMap.collectBy(rNodes,current);
        }
        return rNodes;
    }

    public void removeAllUnmarked(Object mark){
        HaskellNarrowing.removeAllUnmarked(this.nodes,mark);
        for (GenMap genMap : this.params){
            genMap.removeAllUnmarked(mark);
        }
    }

    public void getAll(Set<NarrowNode> target){
        target.addAll(this.nodes);
        for (GenMap genMap : this.params){
            genMap.getAll(target);
        }
    }

}
