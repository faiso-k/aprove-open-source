package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This interface is used by the omegavisitor to carry current inferred type assumptions.
 * it is explicit a haskell object, so the visitors can walk through
 * (especially important for the VarSubstitutor)
 */

public interface Assumptions extends HaskellObject {

    /**
     * rewrites the assumption for the HaskellEntity
     */
    public void pushAssumption(HaskellEntity e,TypeSchema type);

    /**
     * returns the TypeSchema for the HaskellEntity
     */
    public TypeSchema getTypeSchemaFor(HaskellEntity e);

    /**
     * refines the assumptions with a Substitution
     * i.e. it applies the substitution to all contained TypeSchemas
     */
    public void refine(HaskellSubstitution subs);

    /**
     * keeps only the assumptions for the given entities
     */
    public void keepOnly(Collection<HaskellEntity> rEntities);

    /**
     * an Assumptions Skeleton based on a Map
     */
    public class MapSkeleton extends HaskellObject.Visitable implements Assumptions {
        Map<HaskellEntity,TypeSchema> assums;

        public Map<HaskellEntity,TypeSchema> getAssums(){
            return this.assums;
        }

        public void setAssums(Map<HaskellEntity,TypeSchema> assums){
            this.assums = assums;
        }

        public MapSkeleton(){
            this.assums = new HashMap<HaskellEntity,TypeSchema>();
        }

        @Override
        public void pushAssumption(HaskellEntity sym,TypeSchema type){
            this.assums.put(sym,type);
        }

        @Override
        public TypeSchema getTypeSchemaFor(HaskellEntity e){
            return this.assums.get(e);
        }

        @Override
        public void keepOnly(Collection<HaskellEntity> rEntities){
            this.assums.keySet().retainAll(rEntities);
        }

        @Override
        public Object deepcopy(){
            Assumptions.MapSkeleton na = new Assumptions.MapSkeleton();
            for (Map.Entry<HaskellEntity,TypeSchema> entry : this.assums.entrySet()){
                na.assums.put(entry.getKey(),Copy.deep(entry.getValue()));
            }
            return na;
        }

        @Override
        public HaskellObject visit(HaskellVisitor hv){
            if (hv.guardAssumptionEntities(this)){
                Map<HaskellEntity,TypeSchema> nassums = new HashMap<HaskellEntity,TypeSchema>();
                for (Map.Entry<HaskellEntity,TypeSchema> entry : this.assums.entrySet()){
                    nassums.put(this.walk(entry.getKey(),hv),this.walk(entry.getValue(),hv));
                }
                this.assums = nassums;
            } else {
                for (HaskellEntity e : this.assums.keySet()){
                    TypeSchema ts = this.assums.get(e);
                    ts = this.walk(ts,hv);
                    this.assums.put(e,ts);
                }
            }
            return this;
        }

        @Override
        public void refine(HaskellSubstitution subs){
            HaskellVisitor hv = new VarSubstitutor(subs);
            this.visit(hv);
        }

        /**
         * copies all assumptions and adds quantors for all type variables
         * in the TypeSchemas
         */
        public MapSkeleton autoQuanCopy(MapSkeleton assumptions){
            for (Map.Entry<HaskellEntity,TypeSchema> entry : assumptions.assums.entrySet()){
                TypeSchema ts = Copy.deep(entry.getValue());
                ts.autoQuantor();
                this.assums.put(entry.getKey(),ts);
            }
            return this;
        }

        @Override
        public String toString(){
            String r = "";
            for (Map.Entry pair : this.assums.entrySet()){
                r = r + "\n" + pair.getKey() + " :: " + pair.getValue();
            }
            return r;
        }

    }
}
