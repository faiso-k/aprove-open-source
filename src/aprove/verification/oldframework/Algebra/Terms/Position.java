package aprove.verification.oldframework.Algebra.Terms;

import java.io.*;
import java.util.*;

/* This class represents positions in a term or a formula.
 * <p>
 * Note: The first argument of a given function or predicate
 * is labeled as 0.
 * @author Peter Schneider-Kamp
 * @version $Id$
 */

public class Position extends Vector<Integer> implements Iterable<Integer>, Serializable, Comparable<Position> {

    protected Position(Vector<Integer> pos) {
        super(pos);
    }

    static public Position create() {
    return new Position(new Vector<Integer>());
    }

    static public Position create(List<Integer> pos) {
    return new Position(new Vector<Integer>(pos));
    }

    public static Position create(String position) {

        boolean       greater         = false;
        StringBuffer  stringBuffer   = new StringBuffer();
        List<Integer> listOfIntegers = new Vector<Integer>();

        if( position.equals("e") ) {
            return Position.create();
        }

        for(int i=0; i < position.length(); i++) {

            char sign = position.charAt(i);

            if( sign == '(') {

                greater      = true;
                stringBuffer = new StringBuffer();

            } else if( sign == ')') {

                greater = false;
                listOfIntegers.add(Integer.parseInt(stringBuffer.toString()));

            } else {

                if( greater ) {
                    stringBuffer.append(sign);
                } else {
                    listOfIntegers.add(Integer.parseInt(Character.toString(sign)));
                }

            }

        }

        return Position.create(listOfIntegers);
    }

    /* Forbidden for security's and sanity's sake */
    @Override
    public Object clone() {
    throw new RuntimeException("clone deprecated -- use deepcopy / shallowcopy instead");
    }

    /** Returns a shallow copy of this object, i.e. a position
     *  that is represented by the same list of integers.
     */
    public Position shallowcopy() {
        return Position.create(this);
    }

    /* accessor methods */

    /** Concatenate this position with the new subposition given.
     * @param i Subposition that should be appended to this position.
     */
    public Position add(int i) {
        this.add(Integer.valueOf(i));
        return this;
    }

    /** Concatenate this position with the given position.
     */
    public void concatenateWith(Position p){
        for (Integer i : p) {
            this.add(i);
        }
    }


    /** Return a string representation of this position.
     */
    @Override
    public String toString() {
    StringBuffer temp = new StringBuffer();
    if (this.size() == 0) {
        temp.append("e");
    }

    for (Integer p : this) {
            int val = p.intValue();
            if ((0 <= val) && (val < 10)) {
                temp.append(p.toString());
            } else {
                temp.append("(" + p.toString() + ")");
            }
        }
    return temp.toString();
    }

    @Override
    final public boolean equals(Object o) {

        if( o instanceof Position) {
            Position p = (Position)o;
            return super.equals(p);
        }else{
            return false;
        }
    }

    @Override
    final public int hashCode() {
        return this.toString().hashCode();
    }

    /** Check whether this object represents a root position,
     *  i.e. whether this is an empty position.
     */
    public boolean isRootPosition() {
        return this.size() == 0;
    }

     /** Check whether this position is independent from the given
      *  position.
      */
     public boolean isIndependent(Position that) {
     Iterator<Integer> it1 = this.iterator();
     Iterator<Integer> it2 = that.iterator();
     while (it1.hasNext() && it2.hasNext()) {
         if (!it1.next().equals(it2.next())) {
         return true;
         }
     }
     return false;
     }

     /** Returns the predecessor of this position.
      */
     public Position pred() {
     if (this.isRootPosition()) {
         return Position.create();
     }
     Vector<Integer> v = new Vector<Integer>(this);
     v.remove(v.size()-1);
     return new Position(v);
     }

     /** Returns the last element of the position.
      *  If the position is a rootposition the result
      *  is undefined.
      */
     public Integer getLast() {
     return this.get(this.size()-1).intValue();
     }

    /** Returns the maximal position that is below all given positions.
     */
    static public Position getMaximalCommonPosition(Vector<Position> positions) {
    if (positions.isEmpty()) {
        return null;
    }
    Position pos = (Position)positions.remove(0);
    if (positions.isEmpty()) {
        return pos;
    }
    Position npos = Position.create();
    Iterator<Position> it = positions.iterator();
    Vector<Iterator<Integer>> iterators = new Vector<Iterator<Integer>>();
    while (it.hasNext()) {
        iterators.add(it.next().iterator());
    }
    Iterator<Integer> iti = pos.iterator();
    while (iti.hasNext()) {
        Integer i = (Integer)iti.next();
        Iterator<Iterator<Integer>> it2 = iterators.iterator();
        while (it2.hasNext()) {
        Iterator pit = it2.next();
        if (!pit.hasNext() || !i.equals(pit.next())) {
            return npos;
        }
        }
        npos.add(i.intValue());
    }
    return npos;
    }

    @Override
    public int compareTo(Position that) {

        if(this.equals(that)) {
            return 0;
        }

        int min = this.size();

        if( min > that.size()) {
            min = that.size();
        }

        for(int i=0; i < min; i++){
            Integer thisInt = (Integer)this.get(i);
            Integer thatInt = (Integer)that.get(i);

            int returnValue = thisInt.compareTo(thatInt);

            if(returnValue != 0) {
                return returnValue;
            }

        }

        if (that.size() == this.size()){
            return 0;
        }
        else if (that.size() > this.size()){
            return -1;
        }
        else{
            return 1;
        }

    }

    public Position relativate(Position position) {

        Position returnValue = Position.create();

        for(int i= position.size(); i < this.size(); i++) {
            returnValue.add(this.get(i));
        }

        return returnValue;
    }

    public Position deepcopy(){
        Vector<Integer> v = new Vector<Integer>();
        for (Integer i : this) {
            v.add(i);
        }

        return Position.create(v);
    }

    public boolean isSubPosition(Position that) {

        if (that.size() > this.size()){
            return false;
        }

        int min = that.size();

        for(int i=0; i < min; i++){
            Integer thisInt = (Integer)this.get(i);
            Integer thatInt = (Integer)that.get(i);

            boolean returnValue = thisInt.equals(thatInt);

            if(!returnValue) {
                return false;
            }

        }

        return true;

    }

}
