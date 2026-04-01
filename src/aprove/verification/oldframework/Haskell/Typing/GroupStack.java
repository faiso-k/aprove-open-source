package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The GroupStack maps Objects
 * to thier stack level
 *
 */
public class GroupStack<T> {
   protected Map<T,Integer> t2prio;
   protected int counter;

   @Override
public String toString(){
       String out = "[#";
       for (Map.Entry<T,Integer> e : this.t2prio.entrySet()){
           out = out + e.getKey() + "->" + e.getValue()+",";
       }
       return out+"#]";
   }

   public GroupStack(){
       this.t2prio = new LinkedHashMap<T,Integer>();
       this.counter = 0;
   }

   /**
    * create a new group in a new level
    */
   public void pushNewGroup(){
       this.counter = this.counter + 1;
   }

   /**
    * pop the last group
    */
   public void /*Set<T>*/ popGroup(){
       this.counter = this.counter - 1;
       List<T> rem = new ArrayList<T>();
       for (Map.Entry<T,Integer> e : this.t2prio.entrySet()){
          if (e.getValue() > this.counter){
              rem.add(e.getKey());
          }
       }
       this.t2prio.keySet().removeAll(rem);
       /*return rem;*/
   }

   /**
    * checks if an element is in the stack at all
    */
   public boolean contains(T t){
       return this.t2prio.get(t) != null;
   }

   /**
    * removes an element from the stack
    */
   public int remove(T t){
       Integer i = this.t2prio.remove(t);
       if (i == null) {
        return -1;
    }
       return i;
   }

   /**
    * adds an element to a group of a specific level
    * but if this element is already in this group stack with
    * higher level then it is moved to the new lower level
    */
   public void addToGroup(int i,T t){
       Integer j = this.t2prio.get(t);
       if ((j == null) || (j > i)) {
           this.t2prio.put(t,i);
       }
   }

   /**
    * adds some elements to a group of a specific level
    */
   public void addToGroup(int i,Set<T> ts){
       for (T t : ts){
          this.addToGroup(i,t);
       }
   }

   /**
    * adds an element to the top level group
    */
   public void addToPeekGroup(T t){
       this.addToGroup(this.counter,t);
   }


   /**
    * adds some elements to the top level group
    */
   public void addToPeekGroup(Set<T> ts){
       this.addToGroup(this.counter,ts);
   }

   /**
    * @returns the level of an element
    */
   public int getGroupOf(T t){
       Integer i = this.t2prio.get(t);
       if (i == null) {
        return -1;
    }
       return i;
   }

   /**
    * @returns all elements of this stack
    */
   public Set<T> unitedGroups(){
       return this.t2prio.keySet();
   }

}
