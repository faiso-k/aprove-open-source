package aprove.verification.oldframework.Haskell;

import java.util.*;

import aprove.input.Generated.haskell.node.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The HaskellObject is the basic object of all representing, visitable and
 * copyable objects in the Haskell Framework.
 *
 * The HaskellVisitor is only applicable to HaskellObjects
 *
 *
 */
public interface HaskellObject extends Deepcopy, java.io.Serializable {
    HaskellObject visit(HaskellVisitor hv);

    public HaskellObject setToken(Token tok);
    public Token getToken();
    public HaskellObject setTypeTerm(HaskellType t);
    public HaskellType getTypeTerm();
    public HaskellObject transferToken(HaskellObject a);
    public HaskellObject hoCopy(HaskellObject ho);

    /**
     * The Visitable offers convenience for implementing the visit methods
     * of some HaskellObjects, but it don't care about tokens.
     */
    public abstract class Visitable implements HaskellObject {

        @Override
        public HaskellObject setTypeTerm(HaskellType typeTerm){
            return this;
        }

        @Override
        public HaskellType getTypeTerm(){
            return null;
        }

        @Override
        public HaskellObject setToken(Token tok){
            return this;
        }

        @Override
        public Token getToken(){
            return null;
        }

        @Override
        public HaskellObject transferToken(HaskellObject a){
            return a;
        }

        @Override
        public HaskellObject hoCopy(HaskellObject ho){
            return ho.setTypeTerm(Copy.deep(this.getTypeTerm()));
        }

        @Override
        public abstract Object deepcopy();

        /**
         * This methode walks through a HaskellObject by using the
         * visit methode, it does unsafe casts, the given visitor must care
         * of this in case of replacing an object.
         */
        public <E extends HaskellObject> E walk(E wo,HaskellVisitor hw){
            if (wo == null) {
                return null;
            }
            /*if (kill && (wo instanceof HaskellEntity.Skeleton)){
                if (((HaskellEntity.Skeleton) wo).num< 2374) {
                    throw new RuntimeException("herea");
                }
            }*/
            /*if (kill && (wo instanceof HaskellNamedSym)){
                if (((HaskellNamedSym) wo).num< 17374) {
                    HaskellSym.showee(wo);
                    throw new RuntimeException("hereb");
                }
            }*/
            hw.fcaseAll(wo);
            HaskellObject mm = wo.visit(hw);
            if (mm == null) {
                throw new RuntimeException("A null occurs");
            }
            return (E) hw.caseAll(mm);
        }

        /**
         * This methode walks through a collection
         * and each object in the collection is visited by methode walk,
         * also it should only used on collections, which fullfill this argeement:<br/>
         *  col.equals(col.getClass().newInstance().addAll(col))  <br/>
         * <br/>
         * More complex collections should implement HaskellObject
         * and offer thier own visit method, so that method walk could be used.
         *
         * @param source the source collection
         * @param hv the current HaskellVisitor to use.
         * @return a new collection of the same class as source, filled with objects after visit.
         */
        public <E extends HaskellObject,S extends Collection<E>> S listWalk(S source,HaskellVisitor hv){
            if (source == null) {
                return null;
            }
            try {
                Class<? extends Collection> c = source.getClass();
                Collection target = c.newInstance();
                for (E elem : source){
                   target.add(this.walk(elem,hv));
                }
                return (S) target;

            } catch (InstantiationException e){
                 throw new RuntimeException(e);
            } catch (IllegalAccessException e){
                 throw new RuntimeException(e);
            }
        }

    }

    /**
     * This Skeleton is the base of all representing objects,
     * cause it handles also tokens and typeTerms
     */
    public abstract class HaskellObjectSkeleton extends Visitable implements HaskellObject {
        transient Token tok;
        HaskellType typeTerm;

        @Override
        public abstract Object deepcopy();

        @Override
        public HaskellObject setToken(Token tok){
            this.tok = tok;
            return this;
        }

        @Override
        public Token getToken(){
            return this.tok;
        }

        @Override
        public HaskellObject setTypeTerm(HaskellType typeTerm){
            this.typeTerm = typeTerm;
            return this;
        }

        @Override
        public HaskellType getTypeTerm(){
            return this.typeTerm;
        }

        /**
         * This methode transfers a token form one HaskellObject to this one
         * it offers not only convenience, it allows the subclasses to forget
         * the existence of token class.
         */
        @Override
        public HaskellObject transferToken(HaskellObject a){
            this.tok = a.getToken();
            return this;
        }

    }

}




