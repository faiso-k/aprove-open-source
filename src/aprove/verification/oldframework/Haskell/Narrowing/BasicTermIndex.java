package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Modules.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 */

public class BasicTermIndex<E extends BasicTermIndex.Carrier<E>> {
    BasicTermIndex<E> applyIndex; // if the search term has an apply head, this way
    BasicTermIndex<E> universalIndex; // if the search term has a local variable head, this way
    Map<HaskellEntity,BasicTermIndex<E>> entityMap;  // if it is a def-variable or a constructor, this way
    Set<E> elements;

    /**
     * collects all elements in this index-structure (recursive descent)
     * @param target the collection all elements are added to
     */
    public void collectElements(Collection<E> target){
        if (this.elements != null) {
            target.addAll(this.elements);
        }
        if (this.applyIndex != null) {
            this.applyIndex.collectElements(target);
        }
        if (this.universalIndex != null) {
            this.universalIndex.collectElements(target);
        }
        if (this.entityMap != null) {
            for (BasicTermIndex<E> bti : this.entityMap.values()){
                bti.collectElements(target);
            }
        }
    }

    /**
     * @returns the Elements of this index
     */
    public Set<E> getElements(){
        return this.elements;
    }

    /**
     * removes an element from the index-structure
     */
    public void remove(E elem){
         BasicTermIndex<E> bti = elem.getBasicTermIndex();
         if (bti != null) {
              if (bti.getElements() != null) {
                  bti.getElements().remove(elem);
                  elem.setBasicTermIndex(null);
              }
         }
    }

    /**
     * inserts an element in this index-structure
     */
    public void insert(BasicTerm term,E elem){
         this.getCIndex(term).insert(elem);
    }

    /**
     * searches elements matching the current term
     * controlled by the flags
     * @param term the term leading to the elements
     * @param elems collection for found elements
     * @param queryMoreGeneralThanIndex collect all elements of indices which are spezialisations of the term
     * @param indexMoreGeneralThanQuery collect all elements of indices which are more generall than the term
     */
    public void search(BasicTerm term,Collection<E> elems,boolean queryMoreGeneralThanIndex,boolean indexMoreGeneralThanQuery){
        for (BasicTermIndex<E> bti : this.getSIndices(term,queryMoreGeneralThanIndex,indexMoreGeneralThanQuery)){
            elems.addAll(bti.getElements());
        }
    }

    /**
     * inserts an element to this index
     */
    protected void insert(E elem){
         if (this.elements == null) {
             this.elements = new LinkedHashSet<E>();
         }
         elem.setBasicTermIndex(this);
         this.elements.add(elem);
    }

    /**
     * @returns the index the term is pointing to
     */
    protected BasicTermIndex<E> getCIndex(BasicTerm term){
        switch (term.getBasicSort()){
            case APPLY : // to the applyIndex
                Apply apply = (Apply) term;
                if (this.applyIndex == null){
                    this.applyIndex = new BasicTermIndex<E>();
                }
                return this.applyIndex.getCIndex((BasicTerm)apply.getFunction()).getCIndex((BasicTerm)apply.getArgument());
            case VAR: // to the universalIndex
                if (((VarEntity)(((Var) term).getSymbol().getEntity())).getLocal()) {
                    if (this.universalIndex == null){
                        this.universalIndex = new BasicTermIndex<E>();
                    }
                    return this.universalIndex;
                }
            default: // or the entityMap
                HaskellEntity entity = ((Atom)term).getSymbol().getEntity();
                BasicTermIndex<E> bti = null;
                if (this.entityMap != null){
                    bti = this.entityMap.get(entity);
                    if (bti == null) {
                        bti = new BasicTermIndex<E>();
                        this.entityMap.put(entity,bti);
                    }
                } else {
                    bti = new BasicTermIndex<E>();
                    this.entityMap = new HashMap<HaskellEntity,BasicTermIndex<E>>();
                    this.entityMap.put(entity,bti);
                }
                return bti;
        }
    }

    /**
     * @returns a collection of indices fullfilling the search options
     * @param term  serach term
     * @param qmgti queryMoreGeneralThanIndex
     * @param imgtq indexMoreGeneralThanQuery
     */
    protected Collection<BasicTermIndex<E>> getSIndices(BasicTerm term,boolean qmgti,boolean imgtq){
        Collection<BasicTermIndex<E>> res = new LinkedList<BasicTermIndex<E>>();
        if (imgtq && (this.universalIndex != null)) {
            // index more general than query so the universalIndex is needed
            res.add(this.universalIndex); // cause the elements in the universalIndex have
                                          // a local variable at the current position
        }

        // now check the more spezial indices if they fit
        switch (term.getBasicSort()){
            case APPLY : {
                Apply apply = (Apply) term;
                if (this.applyIndex != null){
                    BasicTerm arg = (BasicTerm)apply.getArgument();
                    for (BasicTermIndex<E> bti : this.applyIndex.getSIndices((BasicTerm)apply.getFunction(),qmgti,imgtq)){
                        res.addAll(bti.getSIndices(arg,qmgti,imgtq));
                    }
                }
                return res;
            }
            case VAR:
                if (qmgti && (((VarEntity)(((Var) term).getSymbol().getEntity())).getLocal())) {
                    // query more general than index, all indices are needed (def var, cons or universal)
                    // cause these indices are more spezial, they have explicit constructors or varibales
                    if (this.entityMap != null) {
                        res.addAll(this.entityMap.values());
                    }
                    if ((!imgtq) && qmgti && (this.universalIndex != null)) {
                        // and the search index is more general than a local variable
                        // cause it is a local variable
                        // but only if it is not already in the list;
                        res.add(this.universalIndex);
                    }
                    return res;
                }
                // no break;
            default:
                if (this.entityMap != null) {
                    HaskellEntity entity = ((Atom)term).getSymbol().getEntity();
                    BasicTermIndex<E> bti = this.entityMap.get(entity);
                    if (bti != null) {
                        res.add(bti);
                    }
                }
                // no break;
                return res;
        }

    }

    /**
     * the elements contained in this index implements this interface
     * so they can easily removed.
     */
    public static interface Carrier<E extends Carrier<E>>{
        BasicTermIndex<E> getBasicTermIndex();
        void setBasicTermIndex(BasicTermIndex<E> bti);
    }
}



