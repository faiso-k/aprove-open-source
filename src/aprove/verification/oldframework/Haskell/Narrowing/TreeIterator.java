package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

public class TreeIterator implements Iterator<NarrowNode>{
    List<NarrowNode> level;
    Collection<NarrowNode> noChildrenNodes;
    NarrowNode next;
    Object mark;
    boolean allNodes;


    public TreeIterator(NarrowNode start){
        this.level = new LinkedList<NarrowNode>();
        this.level.add(start);
        this.mark = new Object();
        this.allNodes = false;
    }

    public TreeIterator(NarrowNode start,boolean allNodes){
        this.level = new LinkedList<NarrowNode>();
        this.level.add(start);
        this.mark = new Object();
        this.allNodes = allNodes;
        this.next = null;

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("Collection null-children nodes");
        }
    }

    public TreeIterator(NarrowNode start,Collection<NarrowNode> noChildrenNodes){
        this.level = new LinkedList<NarrowNode>();
        this.level.add(start);
        this.mark = new Object();
        this.allNodes = true;
        this.next = null;
        this.noChildrenNodes = noChildrenNodes;
    }

    @Override
    public boolean hasNext(){
        if (this.next == null) {
            while (!this.level.isEmpty()){
                this.next = this.level.remove(0);
                if (this.next.getMark() != this.mark) {
                    this.next.setMark(this.mark);
                    List<NarrowNode> children = this.next.getChildren();
                    if (children != null) {

                        // XXX DEBUG
                        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                            //System.out.println("chnode: "+next);
                        }

                        this.level.addAll(children);
                    } else {
                        // XXX DEBUG
                        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                            //System.out.println("nochnode: "+next);
                        }

                        if (this.noChildrenNodes != null) {
                            this.noChildrenNodes.add(this.next);
                        }
                    }
                    switch (this.next.getMode()){
                        case INSTANCE : NarrowNode inode = ((InstanceAnnotation)this.next.getAnnotation()).getBase();
                                        // XXX DEBUG
                                        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                                            //              System.out.println("inode: "+inode);
                                        }
                                        this.level.add(inode); break;
                        default: break;
                    }
                    if (this.next.isLinkable()) {
                        if (children != null) {
                            return true;
                        }
                    }
                    if (this.allNodes) {
                        return true;
                    }
                }
            }
            return false;
        } else {
            return true;
        }
    }

    @Override
    public NarrowNode next(){
        if (this.next == null){
            if (!this.hasNext()) {
                throw new RuntimeException("no more values available");
            }
        }
        NarrowNode node = this.next;
        this.next = null;
        return node;
    }

    @Override
    public void remove(){

    }

    public Object markAll(){
        while(this.hasNext()){
            this.next();
        }
        return this.mark;
    }
}

