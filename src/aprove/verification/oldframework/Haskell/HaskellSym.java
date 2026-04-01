package aprove.verification.oldframework.Haskell;

import aprove.verification.oldframework.Haskell.Modules.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * A HaskellSym represent an unique symbol in the whole Haskell Framework,
 * the deepcopy method does nothing, cause HaskellSyms are unique.
 * If you need a fresh unqiue HaskellSym create one with the empty constructor
 * and it is yours, no name generation or other stuff has to be done.
 * The static counter in the class is only for output in toString and has nothing to do with
 * hashCode, equivalentTo or equal methods.
 *
 * Two HaskellSyms are equivalentTo each other if and only if thier references are the same.
 */
public class HaskellSym extends HaskellObject.HaskellObjectSkeleton {
    //private static int counter = 0;
    public static int counter = 0;

    public int num; // don't refer to this number it is only for debug output via toString.

    public HaskellSym() {
        this.num = HaskellSym.counter++;
    }

    public static void show(final Object o) {
        //JTreeDialog.create("Object",new StructureTreeModel(new ReflectTreeEntry("","Object",o))).show();
    }

    public static void show(final String c, final Object o) {
        //JTreeDialog.create(c,new StructureTreeModel(new ReflectTreeEntry("","Object",o))).show();
    }

    public static void showe(final Object o) {
        //JTreeDialog.create("Object",new StructureTreeModel(new ReflectTreeEntry("","Object",o))).show();
    }

    public static void showee(final Object o) {
        // TODO find replacement for JTreeDialog
        //       JTreeDialog.create("Object",new StructureTreeModel(new ReflectTreeEntry("","Object",o))).show();
    }

    @Override
    public Object deepcopy() {
        return this;
    }

    /**
     * Two HaskellSyms are equivalentTo each other if and only if thier references are the same.
     */
    public boolean equivalentTo(final HaskellSym sym) {
        return sym == this;
    }

    /**
     * some symbols have entities, they will overload this methode
     */
    public HaskellEntity getEntity() {
        return null;
    }

    /**
     * some symbols have names, they will overload this methode
     */
    public String getName(final boolean check) {
        return this.toString();
    }

    /**
     * returns true if this symbol is an operator
     * some symbols are operators so they overload this methode
     */
    public boolean getOperator() {
        return false;
    }

    /**
     * some symbols have qualifiers, they will overload this methode
     */
    public String getQualifier() {
        return null;
    }

    /**
     * the tuple symbols are special
     * they overload this method
     */
    public int getTuple() {
        return -1;
    }

    /**
     * return strue,iff this symbol has a name (i.e. it is not annonymous)
     */
    public boolean isNamed() {
        return false;
    }

    /**
     * returns true, iff this symbol is "+"
     */
    public boolean isPlusSym() {
        return false;
    }

    /**
     * returns true, iff this symbol refers the entity
     */
    public boolean matchNQ(final HaskellEntity e) {
        return false;
    }

    /**
     * returns true, iff this symbol refers the entity of the given symbol
     */
    public boolean matchNQ(final HaskellSym e) {
        return false;
    }

    public void setEntity(final HaskellEntity entity) {
    }

    // debug code, shows objects (also non HaskellObjects) by reflection

    /**
     * the entity of a symbol is set by consideration of the current entityFrame and the
     * current sort of this symbols surrounding sort
     */
    public void setEntityPer(final EntityFrame ef, final HaskellEntity.Sort sort) {
        this.setEntity(ef.getLocalEntity(this, sort));
    }

    public void setOperator(final boolean op) {
    }

    public void setTuple(final int i) {
    }

    @Override
    public String toString() {
        return "<" + this.num + ">";
    }

    @Override
    public HaskellObject visit(final HaskellVisitor hv) {
        hv.fcaseHaskellSym(this);
        return hv.caseHaskellSym(this);
    }

}
