package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;


@SuppressWarnings("serial")
public class GenSet extends HashSet<NarrowNode>{
    boolean forced;
    List<Integer> position;

    public GenSet(GenSet nodes){
        super();
        this.setForced(nodes.getForced());
        this.addAll(nodes);
        this.position = new Vector<Integer>(nodes.getPosition());
    }

    public GenSet(){
        super();
        this.forced = false;
        this.position = new Vector<Integer>();
    }

    public boolean getForced(){
        return this.forced;
    }

    public void setForced(boolean forced){
        this.forced = forced;
    }

    public List<Integer> getPosition(){
        return this.position;
    }

    public void setPosition(List<Integer> position){
        this.position = position;
    }

    public boolean check(){
        return this.forced || (this.size() > 1);
    }

    public void addPositionPrefix(int i){
        this.position.add(0,Integer.valueOf(i));

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("Position set:"+i);
        }
    }

    public static GenSet checkAndStart(Set<NarrowNode> nodes,boolean make,boolean forced){
        if (make) {
            GenSet genSet = new GenSet();
            genSet.addAll(nodes);
            genSet.setForced(forced);
            genSet.setPosition(new Vector<Integer>());
            //HaskellSym.showee(nodes);
            return genSet;
        }
        return null;
    }

}

