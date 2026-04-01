package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;

@SuppressWarnings("serial")
public class GenMap extends LinkedHashMap<GenKey,GenEntry>{
    /**
     *
     */
    int depth;
    int pos;
    int num;
    GenParameters genParameters;

    public GenMap(int depth,int pos,GenParameters genParameters){
        this.depth = depth;
        this.pos = pos;
        this.num = HaskellNarrowing.ecount;
        this.genParameters = genParameters;
        HaskellNarrowing.ecount++;
    }

    public GenSet genInsert(NarrowNode node){
        return this.genInsert(node,node.getExpression(),new Stack<GenEntry>());
    }

    public void reorganize(){
        this.symCount(new Stack<GenEntry>());
    }

    protected GenSet genInsert(NarrowNode node, HaskellObject exp,Stack<GenEntry> genEntries){
            List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
            Atom ehead = (Atom) exps.remove(0);
            HaskellEntity entity = ehead.getSymbol().getEntity();
            int arity = exps.size();
            GenKey gk = new GenKey(entity,arity);
            GenEntry ge = this.get(gk);
            if (ge == null) {
                ge = new GenEntry(entity,arity,this.depth+1,this.genParameters);
                ge.increaseAll(genEntries);
                this.put(gk,ge);
            }
            return ge.genInsert(node,exps,genEntries);
    }

    public void removeAll(Collection<NarrowNode> nodes){
            List<GenKey> forRemove = new LinkedList<GenKey>();
            for (Map.Entry<GenKey,GenEntry> entry : this.entrySet()){
                if (entry.getValue().removeAll(nodes)) {
                    forRemove.add(entry.getKey());
                }
            }
            this.keySet().removeAll(forRemove);
    }

    protected void symCount(Stack<GenEntry> genEntries){
            for (Map.Entry<GenKey,GenEntry> entry : this.entrySet()){
                entry.getValue().symCount(genEntries);
            }
    }

    public int getMaxLength(GenSet nodes){
            int mle = 0;
            for (NarrowNode node : nodes){
            int le = node.term.length();
            if (le > mle) {
                mle = le;
            }
            }
            return mle;
    }

    public GenSet collectBy(GenSet nodes,NarrowNode current){
            int i=-1;
            int len = 0;
            GenSet rnodes = new GenSet();
            for (Map.Entry<GenKey,GenEntry> entry : this.entrySet()){
                GenSet cnodes = entry.getValue().collectBy(nodes,current);
                if (cnodes.contains(current)){
                int size = cnodes.size();
                if (size>i){
                    rnodes = cnodes;
                    i = rnodes.size();
                    len = this.getMaxLength(rnodes);
                } else {
                    if (size == i) {
                        int le = this.getMaxLength(cnodes);
                        if (len > le) {
                            rnodes = cnodes;
                            i = rnodes.size();
                            len = le;
                        }
                    }
                }
                }
            }
            return rnodes;
    }

    public void removeAllUnmarked(Object mark){
        for (GenEntry genEntry : this.values()){
            genEntry.removeAllUnmarked(mark);
        }
    }

    public void getAll(Set<NarrowNode> target){
        for (GenEntry genEntry : this.values()){
            genEntry.getAll(target);
        }
    }

    @Override
    public String toString(){
        return this.depth+","+this.pos;
    }

}
